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
  mod = HsModule loc (Module $ "Gen."++fstUpper name) Nothing (mapMaybe import_ prog) (mapMaybe decl prog)
  loc = Hs.SrcLoc (name++".duck") 1 1

import_ :: Loc Ast.Decl -> Maybe HsImportDecl
import_ (Loc l (Ast.Import (V m))) = Just $ HsImportDecl (srcLoc l) (Module $ fstUpper m) False Nothing Nothing
import_ _ = Nothing

decl :: Loc Ast.Decl -> Maybe HsDecl
decl (Loc l (Ast.Data (Loc _ c) vl conses)) = Just $ datatype (srcLoc l) c vl conses
decl _ = Nothing

datatype :: Hs.SrcLoc -> CVar -> [Var] -> [(Loc CVar, [TypePat])] -> HsDecl
datatype l c vl [cons@(_,[_])] = HsNewTypeDecl l [] (name c) (map name vl) (constructor HsUnBangedTy cons) []
datatype l c vl conses = HsDataDecl l [] (name c) (map name vl) (map (constructor HsBangedTy) conses) [] where

constructor :: (HsType -> HsBangType) -> (Loc CVar, [TypePat]) -> HsConDecl
constructor f (Loc l c,tl) = HsConDecl (srcLoc l) (name c) (map (f . typep) tl)

typep :: TypePat -> HsType
typep (TsVar v) = HsTyVar (name v)
typep (TsCons c tl) | isTuple c = HsTyTuple (map typep tl)
typep (TsCons (V "List") [t]) = HsTyApp (HsTyCon (Special HsListCon)) (typep t)
typep (TsCons c tl) = foldl HsTyApp (HsTyCon (UnQual (name c))) (map typep tl)
typep (TsFun [FunArrow s t]) = HsTyFun (typep s) (typep t)
typep t = fatal $ msg $ "Can't convert type" <+> quoted t <+> "to Haskell"

srcLoc :: SrcLoc -> Hs.SrcLoc
srcLoc l | hasLoc l = Hs.SrcLoc (srcFile l++".duck") (srcLine l) (srcCol l) 
srcLoc _ = Hs.SrcLoc "" 0 0

name :: Var -> HsName
name (V s) = HsIdent s

fstUpper :: String -> String
fstUpper [] = []
fstUpper (c:s) = Char.toUpper c : s
