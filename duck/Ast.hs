-- Duck Abstract Syntax Tree

module Ast where

type Var = String

data Exp
  = Let Var Exp
  | Def Var [Var] Exp
  | Apply Exp Exp
  | Seq Exp Exp
  | Var Var
  | Int Int
  deriving Show
