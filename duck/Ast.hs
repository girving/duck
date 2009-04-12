-- Duck Abstract Syntax Tree

module Ast where

import Text.PrettyPrint
import Data.Char
import Data.List

type Var = String

data Exp
  = Set Pattern Exp
  | Def Var [Pattern] Exp
  | Apply Exp [Exp]
  | Seq [Exp]
  | Var Var
  | Int Int
  deriving Show

data Pattern
  = PatVar Var
  | PatTuple [Pattern]
  | PatType Pattern Type
  deriving Show

data Type
  = TyVar Var
  | TyTuple [Type]
  | TyApply Type [Type]
  deriving Show

pretty :: Exp -> Doc
pretty = snd . pexp where
  guard prec = guard_doc prec . pexp
  guard_pat prec = guard_doc prec . ppat
  guard_ty prec = guard_doc prec . pty
  guard_doc prec (inner, doc) =
    if prec > inner then parens doc else doc
  precedence op = case head op of
    '+' -> Just 20
    '-' -> Just 20
    '*' -> Just 30
    '/' -> Just 30 
    _ -> Nothing
  commaspace = text ", "
  pexp e = case e of
    Def f args e -> (0,
      text "def" <+> text f <+> (hsep $ map (guard_pat 2) args) <+> equals
        $$ nest 2 (guard 0 e))
    Seq el -> (0, vcat $ map (guard 0) el)
    Set p e -> (2, guard_pat 0 p <+> equals <+> guard 2 e)
    Apply (Var v) [e1, e2] | Just prec <- precedence v ->
      (prec, (guard prec e1) <+> text v <+> (guard (prec+1) e2) )
    Apply e el -> (50, guard 51 e <+> hsep (map (guard 51) el))
    Var v -> (100,
      if isAlpha (head v) then
        text v
      else parens $ text v)
    Int i -> (100, int i)
  ppat p = case p of
    PatVar v -> (100, text v)
    PatTuple pl -> (1, sep $ intersperse commaspace $ map (guard_pat 2) pl)
    PatType p t -> (2, guard_pat 2 p <+> colon <+> guard_ty 0 t)
  pty t = case t of
    TyVar v -> (100, text v)
    TyTuple tl -> (2, sep $ intersperse commaspace $ map (guard_ty 3) tl)
    TyApply t tl -> (50, guard_ty 50 t <+> hsep (map (guard_ty 51) tl))
