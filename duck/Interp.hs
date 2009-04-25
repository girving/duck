-- Duck interpreter

-- For now, this is dynamically typed

module Interp where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Var
import Pretty
import Text.PrettyPrint
import qualified Ir
import Data.Map (Map)
import qualified Data.Map as Map

type Env = Map Var Value

data Value
  = ValInt Int
  | ValCons Var [Value]
  | ValFun Env Var Ir.Exp
  | ValBuiltin Var Int [Value] ([Value] -> Value)

-- Process a list of definitions into an environment.
-- This function is currently globally lazy, since it passes the
-- global environment to decl before it has been build.  Since
-- duck is _not_ implicitly lazy, this will need to be replaced
-- with an appropriate topological sort to find a cycle free
-- definition order.
prog :: [Ir.Decl] -> Env
prog decls = env where
  env = foldl (decl env) prelude decls

-- The first environment contains all global definitions,
-- and isn't defined until after decl completes
decl :: Env -> Env -> Ir.Decl -> Env
decl globals env (Ir.LetD v e) = Map.insert v (expr globals e) env
decl globals env (Ir.OverD v _ e) = Map.insert v (expr globals e) env
decl _ env (Ir.Data _ _ cases) = foldl f env cases where
  f :: Env -> (CVar, [a]) -> Env
  f env (c,args) = Map.insert c (expr Map.empty ir) env where
    ir = foldr Ir.Lambda (Ir.Cons c (map Ir.Var vl)) vl
    vl = vars 0 args
    vars _ [] = []
    vars i (_:rest) = V ("x" ++ show i) : vars (i+1) rest

lookup :: Env -> Var -> Value
lookup env v | Just r <- Map.lookup v env = r
             | otherwise = error ("unbound variable " ++ show v)

expr :: Env -> Ir.Exp -> Value
expr env = e where
  e (Ir.Int i) = ValInt i
  e (Ir.Var v) = lookup env v
  e (Ir.Lambda v e) = ValFun env v e
  e (Ir.Apply e1 e2) = case v1 of
      ValBuiltin v arity args f ->
        let args' = v2 : args in
        if length args' == arity then f (reverse args')
        else ValBuiltin v arity args' f
      ValFun env' v e -> expr (Map.insert v v2 env') e
      _ -> error ("expected a -> b, got " ++ show (pretty v1))
      where v1 = expr env e1
            v2 = expr env e2
  e (Ir.Let v e body) = expr (Map.insert v (expr env e) env) body
  e (Ir.Case e pl def) = case d of
      ValCons c dl -> case find (\ (c',_,_) -> c == c') pl of
        Just (_,vl,e') -> expr (foldl (\s (v,d) -> Map.insert v d s) env (zip vl dl)) e'
        Nothing -> case def of
          Nothing -> error ("pattern match failed")
          Just (v,e') -> expr (Map.insert v d env) e' 
      _ -> error ("expected block, got " ++ show (pretty d))
      where d = expr env e
  e (Ir.Cons c el) = ValCons c (map (expr env) el)

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
  pretty' (ValInt i) = pretty' i
  pretty' (ValCons c fields) = (1, pretty c <+> sep (map (guard 2) fields))
  pretty' (ValFun _ v e) = -- conveniently ignore env
    (0, text "\\" <> pretty v <> text " -> " <> pretty e)
  pretty' (ValBuiltin v _ _ _) = pretty' v
