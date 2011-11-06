-- | Generate Haskell code from Duck Ast

module ToHaskell
  ( prog )
  where

import Data.Maybe 
import Data.List
import qualified Data.Char as Char
import Pretty
import Stage
import Var
import SrcLoc hiding (srcLoc)
import IrType
import qualified Ast
import Language.Haskell.Syntax hiding (SrcLoc, srcLine)
import qualified Language.Haskell.Syntax as Hs
import qualified Language.Haskell.Pretty as PHs

prog :: String -> Ast.Prog -> Doc'
prog name prog = header $+$ PHs.prettyPrintWithMode (PHs.defaultMode { PHs.linePragmas = True }) mod where
  header = "{- Generated from \""++name++".duck\" automatically; do not edit! -}"
  mod = HsModule loc (Module $ "Gen."++fstUpper name) Nothing (catMaybes (value : map import_ prog)) (concatMap (decl doConvert) prog)
  loc = Hs.SrcLoc (name++".duck") 1 1
  value = if doConvert then Just $ HsImportDecl loc (Module "Memory") False Nothing Nothing else Nothing
  doConvert = name /= "memory"

import_ :: Loc Ast.Decl -> Maybe HsImportDecl
import_ (L l (Ast.Import (V m))) = Just $ HsImportDecl (srcLoc l) (Module $ fstUpper m) False Nothing Nothing
import_ _ = Nothing

decl :: Bool -> Loc Ast.Decl -> [HsDecl]
decl doConvert (L l (Ast.Data (L _ c) vl conses)) = datatype l' c' vl' conses : convert doConvert l' c' vl' conses where
  l' = srcLoc l
  c' = name c
  vl' = map name vl
decl _ _ = []

datatype :: Hs.SrcLoc -> Hs.HsName -> [Hs.HsName] -> [(Loc CVar, [TypePat])] -> HsDecl
datatype l c vl [cons@(_,[_])] = HsNewTypeDecl l [] c vl (constructor HsUnBangedTy cons) []
datatype l c vl conses = HsDataDecl l [] c vl (map (constructor HsBangedTy) conses) [] where

constructor :: (HsType -> HsBangType) -> (Loc CVar, [TypePat]) -> HsConDecl
constructor f (L l c,tl) = HsConDecl (srcLoc l) (name c) (map (f . typep) tl)

typep :: TypePat -> HsType
typep (TsVar v) = HsTyVar (name v)
typep (TsCons c tl) | isTuple c = HsTyTuple (map typep tl)
typep (TsCons (V "List") [TsCons (V "Char") []]) = HsTyCon (UnQual (HsIdent "String"))
typep (TsCons (V "List") [t]) = HsTyApp (HsTyCon (Special HsListCon)) (typep t)
typep (TsCons c tl) = foldl HsTyApp (HsTyCon (UnQual (name c))) (map typep tl)
typep (TsFun [FunArrow s t]) = HsTyFun (typep s) (typep t)
typep t = fatal $ msg $ "Can't convert type" <+> quoted t <+> "to Haskell"

convert :: Bool -> Hs.SrcLoc -> HsName -> [HsName] -> [(Loc CVar, [TypePat])] -> [HsDecl]
convert True l tc vl conses = [HsInstDecl l context convert' [ty] [value,unsafeUnvalue]] where
  convert' = UnQual (HsIdent "Convert")
  valcons = UnQual (HsIdent "valCons")
  ty = foldl HsTyApp (HsTyCon (UnQual tc)) (map HsTyVar vl)
  context = map (\v -> (convert', [HsTyVar v])) vl
  value = HsFunBind (map f (zip [0..] conses)) where
    f (i,(L _ c, args)) = HsMatch l value' [HsPApp (UnQual (name c)) (map HsPVar vl)] (HsUnGuardedRhs e) [] where
      e = HsApp (HsApp (HsCon valcons) (HsLit (HsInt i))) (HsList (map (\v -> HsApp (HsVar (UnQual value')) (HsVar (UnQual v))) vl))
      vl = map name (take (length args) standardVars)
    value' = HsIdent "value"
  unsafeUnvalue = HsFunBind [HsMatch l unsafeUnvalue' [valpat] (HsUnGuardedRhs e) []] where
    valpat = case conses of
      [(_,[])] -> HsPWildCard
      _ -> HsPVar val
    e = case conses of
      [c] -> extract c
      _ -> HsCase (HsApp unsafeTag (HsVar (UnQual val))) (map cons (zip [0..] conses) ++ [fail])
    cons :: (Integer,(Loc CVar,[TypePat])) -> HsAlt
    cons (i,c@(L l _,_)) = HsAlt (srcLoc l) (HsPLit (HsInt i)) (HsUnGuardedAlt (extract c)) [] where
    extract (L l c,tl) = case vl of
      [] -> cons []
      [_] -> cons [HsParen rhs]
      _ -> HsLet [HsPatBind (srcLoc l) pat (HsUnGuardedRhs rhs) []] (cons $ map (HsVar . UnQual) vl)
      where
      cons args = foldl' HsApp (HsCon (UnQual (name c))) (map (HsParen . (HsApp $ HsVar $ UnQual unsafeUnvalue')) args)
      pat = case map HsPVar vl of
        [v] -> v
        vl -> HsPTuple vl
      rhs = HsApp unsafeUnvalCons (HsVar (UnQual val))
      vl = map name (take (length tl) standardVars)
    fail :: HsAlt
    fail = HsAlt l HsPWildCard (HsUnGuardedAlt (HsApp error' (HsLit $ HsString $ show $ "bad tag in unsafeUnvalue" <+> tc'))) []
      where HsIdent tc' = tc
    unsafeUnvalue' = HsIdent "unsafeUnvalue"
    unsafeUnvalCons = HsVar $ UnQual $ HsIdent "unsafeUnvalCons"
    unsafeTag = HsVar $ UnQual $ HsIdent "unsafeTag"
    error' = HsVar $ UnQual $ HsIdent "error"
    val = HsIdent "val"
convert False _ _ _ _ = []

srcLoc :: SrcLoc -> Hs.SrcLoc
srcLoc l | hasLoc l = Hs.SrcLoc (srcFile l++".duck") (srcLine l) (srcCol l) 
srcLoc _ = Hs.SrcLoc "" 0 0

name :: Var -> HsName
name (V s) = HsIdent s

fstUpper :: String -> String
fstUpper [] = []
fstUpper (c:s) = Char.toUpper c : s
