-- Duck interpreter

-- For now, this is dynamically typed

module Interp where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Var
import Pretty
import Text.PrettyPrint
import qualified Ast
import qualified Ir
import Data.Map (Map)
import qualified Data.Map as Map

type Env = Map Var Value

data Value
  = ValInt Int
  | ValCons Var [Value]
  | ValFun Env Var Ir.Exp
  | ValBuiltin Var Int [Value] ([Value] -> Value)

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: [Ir.Decl] -> Env
prog = foldl decl prelude

-- The first environment contains all global definitions,
-- and isn't defined until after decl completes
decl :: Env -> Ir.Decl -> Env
decl global (Ir.LetD v e) = Map.insert v (expr global Map.empty e) global
decl global (Ir.LetMD vl e) = foldl (\s (v,d) -> Map.insert v d s) global (zip vl dl) where
  dl = case expr global Map.empty e of
    ValCons c dl | istuple c, length vl == length dl -> dl
    d -> error ("expected "++show (length vl)++"-tuple, got "++show (pretty d))
decl global (Ir.OverD v _ e) = Map.insert v (expr global Map.empty e) global
decl global (Ir.Data _ _ cases) = foldl f global cases where
  f :: Env -> (CVar, [a]) -> Env
  f global (c,args) = Map.insert c (expr global Map.empty ir) global where
    ir = foldr Ir.Lambda (Ir.Cons c (map Ir.Var vl)) vl
    vl = take (length args) standardVars

lookup :: Env -> Env -> Var -> Value
lookup global env v
  | Just r <- Map.lookup v env = r -- check for local definitions first
  | Just r <- Map.lookup v global = r -- fall back to global definitions
  | otherwise = error ("unbound variable " ++ show v)

expr :: Env -> Env -> Ir.Exp -> Value
expr global env = exp where
  exp (Ir.Int i) = ValInt i
  exp (Ir.Var v) = lookup global env v
  exp (Ir.Lambda v e) = ValFun env v e
  exp (Ir.Apply e1 e2) = case v1 of
    ValBuiltin v arity args f ->
      let args' = v2 : args in
      if length args' == arity then f (reverse args')
      else ValBuiltin v arity args' f
    ValFun env' v e -> expr global (Map.insert v v2 env') e
    _ -> error ("expected a -> b, got " ++ show (pretty v1))
    where v1 = exp e1
          v2 = exp e2
  exp (Ir.Let v e body) = expr global (Map.insert v (exp e) env) body
  exp (Ir.Case e pl def) = case d of
    ValCons c dl -> case find (\ (c',_,_) -> c == c') pl of
      Just (_,vl,e') -> expr global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl dl)) e'
      Nothing -> case def of
        Nothing -> error ("pattern match failed: exp = " ++ show (pretty d) ++ ", cases = " ++ show pl)
        Just (v,e') -> expr global (Map.insert v d env) e' 
    _ -> error ("expected block, got " ++ show (pretty d))
    where d = exp e
  exp (Ir.Cons c el) = ValCons c (map exp el)

prelude :: Env
prelude = decTuples (Map.fromList binops) where
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
  decTuples global = foldl decTuple global (0 : [2..5])
  decTuple global i = decl global (Ir.Data c vars [(c, map Ast.TyVar vars)]) where
    c = tuple vars
    vars = take i standardVars

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValCons c []) = pretty' c
  pretty' (ValCons c fields) = (1, pretty c <+> sep (map (guard 2) fields))
  pretty' (ValFun _ v e) = -- conveniently ignore env
    (0, text "\\" <> pretty v <> text " -> " <> pretty e)
  pretty' (ValBuiltin v _ _ _) = pretty' v
