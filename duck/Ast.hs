-- Duck Abstract Syntax Tree

module Ast where

import Text.PrettyPrint
import Data.Char
import Data.List

type Var = String

type Prog = [Decl]

data Decl
  = DefD Var [Pattern] Exp
  | LetD Pattern Exp
  deriving Show

data Exp
  = Set Pattern Exp
  | Def Var [Pattern] Exp Exp
  | Let Pattern Exp Exp
  | Lambda [Pattern] Exp
  | Apply Exp [Exp]
  | Seq [Exp]
  | Var Var
  | Int Int
  deriving Show

data Pattern
  = PatAny
  | PatVar Var
  | PatTuple [Pattern]
  | PatType Pattern Type
  deriving Show

data Type
  = TyVar Var
  | TyTuple [Type]
  | TyApply Type [Type]
  deriving Show


class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)

  pretty = snd . pretty'
  pretty' t = (0, pretty t)

guard :: Pretty t => Int -> t -> Doc
guard prec x
  | prec > inner = parens doc
  | otherwise = doc
  where (inner, doc) = pretty' x

instance Pretty t => Pretty [t] where
  pretty = vcat . map (guard 0)

instance Pretty Decl where
  pretty (LetD p e) =
    text "let" <+> pretty p <+> equals <+> pretty e
  pretty (DefD f args e) =
    text "let" <+> text f <+> hsep (map (guard 2) args) <+> equals
      $$ nest 2 (guard 0 e)

precedence op = case head op of
  '+' -> Just 20
  '-' -> Just 20
  '*' -> Just 30
  '/' -> Just 30 
  _ -> Nothing

instance Pretty Exp where
  pretty' (Let p e body) = (0,
    text "let" <+> pretty p <+> equals <+> guard 0 e <+> text "in"
      $$ (guard 0 body))
  pretty' (Def f args e body) = (0,
    text "let" <+> text f <+> hsep (map (guard 2) args) <+> equals
      $$ nest 2 (guard 0 e) <+> text "in" $$ (guard 0 body))
  pretty' (Lambda args e) = (5,
    text "\\" <> hsep (map (guard 2) args) <+> text "->" <+> guard 5 e)
  pretty' (Seq el) = (0, vcat $ map (guard 0) el)
  pretty' (Set p e) = (2, guard 0 p <+> equals <+> guard 2 e)
  pretty' (Apply (Var v) [e1, e2]) | Just prec <- precedence v =
    (prec, (guard prec e1) <+> text v <+> (guard (prec+1) e2) )
  pretty' (Apply e el) = (50, guard 51 e <+> hsep (map (guard 51) el))
  pretty' (Var v) = (100,
    if isAlpha (head v) then
      text v
    else parens $ text v)
  pretty' (Int i) = (100, int i)

instance Pretty Pattern where
  pretty' (PatAny) = (100, text "_")
  pretty' (PatVar v) = (100, text v)
  pretty' (PatTuple pl) = (1, sep $ intersperse (text ", ") $ map (guard 2) pl)
  pretty' (PatType p t) = (2, guard 2 p <+> colon <+> guard 0 t)

instance Pretty Type where
  pretty' (TyVar v) = (100, text v)
  pretty' (TyTuple tl) = (2, sep $ intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TyApply t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
