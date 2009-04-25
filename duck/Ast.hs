-- Duck Abstract Syntax Tree

module Ast where

import Var
import Pretty
import Text.PrettyPrint
import Data.List

type Prog = [Decl]

data Decl
  = DefD Var (Maybe Type) [Pattern] Exp
  | LetD Pattern Exp
  | Data CVar [Var] [(CVar,[Type])]
  deriving Show

data Exp
  = Def Var [Pattern] Exp Exp
  | Let Pattern Exp Exp
  | Lambda [Pattern] Exp
  | Apply Exp [Exp]
  | Var Var
  | Int Int
  | Case Exp [(Pattern,Exp)]
  deriving Show

data Pattern
  = PatAny
  | PatVar Var
  | PatCons CVar [Pattern]
  | PatType Pattern Type
  deriving Show

data Type
  = TyVar Var
  | TyTuple [Type]
  | TyApply CVar [Type]
  | TyFun Type Type
  deriving Show

-- Pretty printing

instance Pretty Decl where
  pretty (LetD p e) =
    text "let" <+> pretty p <+> equals <+> pretty e
  pretty (DefD f mt args e) =
    maybe empty (\t -> text "over" <+> pretty t) mt $$
    text "let" <+> pretty f <+> hsep (map (guard 2) args) <+> equals
      $$ nest 2 (guard 0 e)
  pretty (Data t args []) =
    text "data" <+> pretty t <+> hsep (map pretty args)
  pretty (Data t args (hd:tl)) =
    text "data" <+> pretty t <+> hsep (map pretty args) $$ nest 2 (vcat (
      (equals <+> f hd) : map (\x -> text "|" <+> f x) tl))
    where f (c,args) = hsep (pretty c : map (guard 60) args)

instance Pretty Exp where
  pretty' (Let p e body) = (0,
    text "let" <+> pretty p <+> equals <+> guard 0 e <+> text "in"
      $$ (guard 0 body))
  pretty' (Def f args e body) = (0,
    text "let" <+> pretty f <+> hsep (map (guard 2) args) <+> equals
      $$ nest 2 (guard 0 e) <+> text "in" $$ (guard 0 body))
  pretty' (Lambda args e) = (5,
    text "\\" <> hsep (map (guard 2) args) <+> text "->" <+> guard 5 e)
  pretty' (Apply (Var v) [e1, e2]) | Just prec <- precedence v =
    let V s = v in
    (prec, (guard prec e1) <+> text s <+> (guard (prec+1) e2) )
  pretty' (Apply e el) = (50, guard 51 e <+> hsep (map (guard 51) el))
  pretty' (Var v) = pretty' v
  pretty' (Int i) = pretty' i
  pretty' (Case e cases) = (0,
    text "case" <+> pretty e <+> text "of" $$ nest 2 (
      vjoin '|' (map (\ (p,e) -> pretty p <+> text "->" <+> pretty e) cases)))

instance Pretty Pattern where
  pretty' (PatAny) = pretty' '_'
  pretty' (PatVar v) = pretty' v
  pretty' (PatCons c pl) = (1, pretty c <+> sep (map (guard 2) pl))
  -- pretty' (PatTuple pl) = (1, sep $ intersperse (text ", ") $ map (guard 2) pl)
  pretty' (PatType p t) = (2, guard 2 p <+> colon <+> guard 0 t)

instance Pretty Type where
  pretty' (TyVar v) = pretty' v
  pretty' (TyTuple tl) = (2, sep $ intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TyApply t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
  pretty' (TyFun t1 t2) = (1, guard 2 t1 <+> text "->" <+> guard 1 t2)
