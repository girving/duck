-- Duck Abstract Syntax Tree

module Ast where

import Text.PrettyPrint as PP
import Data.Char

type Var = String

data Exp
  = Let Var Exp
  | Def Var [Var] Exp
  | Apply Exp Exp
  | Seq Exp Exp
  | Var Var
  | Int Int

pretty :: Exp -> PP.Doc
pretty = snd . helper where
  guard prec e =
    if prec > inner then parens doc else doc
    where (inner, doc) = helper e
  precedence op = case head op of
    '+' -> Just 20
    '-' -> Just 20
    '*' -> Just 30
    '/' -> Just 30 
    _ -> Nothing
  helper e = case e of
    Def f args e -> (0,
      (hsep $ map PP.text (f:args)) <+> PP.equals
        $$ nest 2 (guard 0 e))
    Seq e1 e2 -> (0, (guard 0 e1) $$ (guard 0 e2))
    Let v e -> (2, PP.text v <+> guard 2 e)
    Apply (Apply (Var v) e1) e2 | Just prec <- precedence v ->
      (prec, (guard prec e1) <+> PP.text v <+> (guard (prec+1) e2) )
    Apply e1 e2 -> (50, guard 50 e1 <+> guard 51 e2)
    Var v -> (100,
      if isAlpha (head v) then
        PP.text v
      else parens $ PP.text v)
    Int i -> (100, PP.int i)

instance Show Exp where
  show = PP.render . pretty
