-- | Generate Haskell code from Duck Ast

module ToHaskell
  ( prog )
  where

import Data.Maybe 
import qualified Data.Char as Char
import Pretty
import Stage
import Var
import SrcLoc hiding (srcLoc)
import Type
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
typep (TsCons (V "List") [t]) = HsTyApp (HsTyCon (Special HsListCon)) (typep t)
typep (TsCons c tl) = foldl HsTyApp (HsTyCon (UnQual (name c))) (map typep tl)
typep (TsFun [FunArrow s t]) = HsTyFun (typep s) (typep t)
typep t = fatal $ msg $ "Can't convert type" <+> quoted t <+> "to Haskell"

convert :: Bool -> Hs.SrcLoc -> HsName -> [HsName] -> [(Loc CVar, [TypePat])] -> [HsDecl]
convert True l c vl conses = [HsInstDecl l context convert' [ty] [value,unvalue]] where
  convert' = UnQual (HsIdent "Convert")
  valcons = UnQual (HsIdent "ValCons")
  ty = foldl HsTyApp (HsTyCon (UnQual c)) (map HsTyVar vl)
  context = map (\v -> (convert', [HsTyVar v])) vl
  value = HsFunBind (map f (zip [0..] conses)) where
    f (i,(L _ c, args)) = HsMatch l value' [HsPApp (UnQual (name c)) (map HsPVar vl)] (HsUnGuardedRhs e) [] where
      e = HsApp (HsApp (HsCon valcons) (HsLit (HsInt i))) (HsList (map (\v -> HsApp (HsVar (UnQual value')) (HsVar (UnQual v))) vl))
      vl = map name (take (length args) standardVars)
    value' = HsIdent "value"
  unvalue = HsFunBind (map f (zip [0..] conses) ++ [fail]) where
    f (i,(L _ c, args)) = HsMatch l unvalue' [HsPApp valcons [HsPLit (HsInt i), HsPList (map HsPVar vl)]] (HsUnGuardedRhs e) [] where
      e = foldl HsApp (HsCon (UnQual (name c))) (map (\v -> HsParen $ HsApp (HsVar (UnQual unvalue')) (HsVar (UnQual v))) vl)
      vl = map name (take (length args) standardVars)
    fail = HsMatch l unvalue' [HsPWildCard] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "undefined")))) []
    unvalue' = HsIdent "unvalue"
convert False _ _ _ _ = []

srcLoc :: SrcLoc -> Hs.SrcLoc
srcLoc l | hasLoc l = Hs.SrcLoc (srcFile l++".duck") (srcLine l) (srcCol l) 
srcLoc _ = Hs.SrcLoc "" 0 0

name :: Var -> HsName
name (V s) = HsIdent s

fstUpper :: String -> String
fstUpper [] = []
fstUpper (c:s) = Char.toUpper c : s
