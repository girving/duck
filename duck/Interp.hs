-- Duck interpreter

-- For now, this is dynamically typed

module Interp where

import Prelude hiding (lookup)
import Var
import Pretty
import Text.PrettyPrint
import qualified Ir
import Data.Map (Map)
import qualified Data.Map as Map

type Env = Map Var Value

data Value
  = ValInt Int
  | ValFun Env Var Ir.Exp
  | ValBuiltin Var Int [Value] ([Value] -> Value)

prog :: [Ir.Decl] -> Env
prog = foldl (\env (Ir.LetD v e) -> Map.insert v (expr env e) env) prelude

lookup :: Env -> Var -> Value
lookup env v | Just r <- Map.lookup v env = r
             | otherwise = error ("unbound variable " ++ show v)

expr :: Env -> Ir.Exp -> Value
expr env = e where
  e (Ir.Int i) = ValInt i
  e (Ir.Var v) = lookup env v
  e (Ir.Lambda v e) = ValFun env v e
  e (Ir.Apply e1 e2) = case v1 of
      ValInt i -> error ("expected a -> b, got " ++ show i)
      ValBuiltin v arity args f ->
        let args' = v2 : args in
        if length args' == arity then f (reverse args')
        else ValBuiltin v arity args' f
      ValFun env' v e -> expr (Map.insert v v2 env') e
      where v1 = expr env e1
            v2 = expr env e2
  e (Ir.Let v e body) = expr (Map.insert v (expr env e) env) body

prelude :: Env
prelude = Map.fromList binops where
  binops = map binop
    [ ("+", (+))
    , ("-", (-))
    , ("*", (*))
    , ("/", div) ]
  binop :: (String, Int -> Int -> Int) -> (Var, Value)
  binop (s,f) = (v, ValBuiltin v 2 [] (\[a,b] -> f' a b)) where
    v = V s
    f' (ValInt a) (ValInt b) = ValInt (f a b)
    f' a b = error ("expected (int, int), got (" ++ show (pretty a) ++ ", " ++ show (pretty b) ++ ")")

-- Pretty printing

instance Pretty Value where
  pretty (ValInt i) = pretty i
  pretty (ValFun _ v e) = -- conveniently ignore env
    text "\\" <> pretty v <> text " -> " <> pretty e
  pretty (ValBuiltin v _ _ _) = pretty v
