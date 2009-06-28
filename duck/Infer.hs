{-# LANGUAGE PatternGuards #-}
-- Duck type inference

module Infer
  ( prog
  ) where

import Var
import Type
import Util
import Pretty
import Lir (Prog, Datatype, Overload)
import qualified Lir
import qualified Data.Map as Map
import Data.List hiding (lookup)
import qualified Data.List
import Control.Monad hiding (guard)
import InferMonad hiding (lookup)
import Prelude hiding (lookup)
import qualified Prims
import Data.Maybe
import qualified Data.List as List

---- Algorithm discussion:

-- The state of the type inference algorithm consists of
--
-- 1. A set of function type primitives (functors) representing maps from types to types.
-- 2. A map from variables to (possibly primitive) types.
-- 3. A set of in-progress type applications to compute fixed points in the case of recursion.

-- Some aliases for documentation purposes

type Globals = TypeEnv
type Locals = TypeEnv

-- Utility functions

lookup :: Prog -> Globals -> Locals -> Var -> Infer Type
lookup prog global env v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v global = return r -- fall back to global definitions
  | Just _ <- Map.lookup v (Lir.functions prog) = return $ TyApply v [] -- if we find overloads, make a new closure
  | otherwise = typeError ("unbound variable " ++ show v)

lookupDatatype :: Prog -> CVar -> Infer Datatype
lookupDatatype prog tv
  | Just d <- Map.lookup tv (Lir.datatypes prog) = return d
  | otherwise = typeError ("unbound datatype constructor " ++ show tv)

lookupOverloads :: Prog -> Var -> Infer [Overload]
lookupOverloads prog f
  | Just o <- Map.lookup f (Lir.functions prog) = return o
  | otherwise = typeError ("unbound function " ++ show f)

lookupConstructor :: Prog -> Var -> Infer (CVar, [Var], [Type])
lookupConstructor prog c
  | Just tc <- Map.lookup c (Lir.conses prog)
  , Just (vl,cases) <- Map.lookup tc (Lir.datatypes prog)
  , Just tl <- Data.List.lookup c cases = return (tc,vl,tl)
  | otherwise = typeError ("unbound constructor " ++ show c)

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Lir.Prog -> Infer Globals
prog prog = foldM (statement prog) Map.empty (Lir.statements prog)

statement :: Prog -> Globals -> ([Var], Lir.Exp) -> Infer Globals
statement prog env (vl,e) = do
  t <- expr prog env Map.empty e
  tl <- case (vl,t) of
          ([_],_) -> return [t]
          (_, TyApply c tl) | istuple c, length vl == length tl -> return tl
          _ -> typeError ("expected "++show (length vl)++"-tuple, got "++show (pretty t))
  return $ foldl (\g (v,t) -> Map.insert v t g) env (zip vl tl)

expr :: Prog -> Globals -> Locals -> Lir.Exp -> Infer Type
expr prog global env = exp where
  exp (Lir.Int _) = return TyInt
  exp (Lir.Var v) = lookup prog global env v
  exp (Lir.Apply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    case t1 of
      TyApply f args -> apply prog global f (args ++ [t2])
      _ -> typeError ("expected a -> b, got " ++ show (pretty t1))
  exp (Lir.Let v e body) = do
    t <- exp e
    expr prog global (Map.insert v t env) body
  exp (Lir.Case e pl def) = do
    t <- exp e
    case t of
      TyApply tv types -> do
        (tvl, cases) <- lookupDatatype prog tv
        let tenv = Map.fromList (zip tvl types)
            caseType (c,vl,e')
              | Just tl <- List.lookup c cases, a <- length tl =
                  if length vl == a then
                    expr prog global (foldl (\e (v,t) -> Map.insert v t e) env (zip vl (map (subst tenv) tl))) e'
                  else
                    typeError ("arity mismatch in pattern: "++show (pretty c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
                      ++" but got ["++concat (intersperse ", " (map (show . pretty) vl))++"]")
              | otherwise = typeError ("datatype "++show (pretty tv)++" has no constructor "++show (pretty c))
            defaultType Nothing = return []
            defaultType (Just (v,e')) = expr prog global (Map.insert v t env) e' >.= \t -> [t]
            join t1 t2 | Just t <- unifyS t1 t2 = return t
                       | otherwise = typeError ("failed to unify types "++show (pretty t1)++" and "++show (pretty t2)++" from different case branches")
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        foldM1 join (caseResults ++ defaultResults)
      _ -> typeError ("expected datatype, got "++show (pretty t))
  exp (Lir.Cons c el) = do
    args <- mapM exp el
    (tv,vl,tl) <- lookupConstructor prog c
    case unifyList tl args of
      Nothing -> typeError (show (pretty c)++" expected arguments "++showlist tl++", got "++showlist args) where
        showlist = unwords . map (show . guard 51)
      Just tenv -> return $ TyApply tv targs where
        targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
  exp (Lir.Binop op e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    Prims.primType op t1 t2
  exp (Lir.Bind v e1 e2) = do
    t <- runIO =<< exp e1
    t <- expr prog global (Map.insert v t env) e2
    checkIO t
  exp (Lir.Return e) = exp e >.= TyIO
  exp (Lir.PrimIO p el) = mapM exp el >>= Prims.primIOType p >.= TyIO

-- Overloaded function application
apply :: Prog -> Globals -> Var -> [Type] -> Infer Type
apply prog global f args = do
  rawOverloads <- lookupOverloads prog f -- look up possibilities
  let call = unwords (map show (pretty f : map (guard 51) args))
      prune o@(tl,_,_,_) = case unifyList tl args of
        Just _ -> Just o
        Nothing -> Nothing
      overloads = catMaybes (map prune rawOverloads) -- prune those that don't match
      isSpecOf a b = isJust (unifyList b a)
      isMinimal (tl,_,_,_) = all (\ (tl',_,_,_) -> isSpecOf tl tl' || not (isSpecOf tl' tl)) overloads
      options overs = concatMap (\ (tl,r,_,_) -> concat ("\n  " : intersperse " -> " (map (show . guard 2) (tl ++ [r])))) overs
  case filter isMinimal overloads of -- prune away overloads which are more general than some other overload
    [] -> typeError (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition (\ (_,_,l,_) -> length l == length args) os of
      ([],_) -> return $ TyApply f args -- all overloads are still partially applied
      ([(_,_,vl,e)],[]) -> withFrame f args $ -- exactly one fully applied option
        expr prog global (foldl (\env (v,t) -> Map.insert v t env) Map.empty (zip vl args)) e
      (fully@(_:_),partially@(_:_)) -> typeError (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)
      (fully@(_:_:_),[]) -> typeError (call++" is ambiguous, possibilities are"++options fully)

-- This is the analog for Interp.runIO for types.  It exists by analogy even though it is very simple.
runIO :: Type -> Infer Type
runIO (TyIO t) = return t
runIO t = typeError ("expected IO type, got "++show (pretty t))

-- Verify that a type is in IO, and leave it unchanged if so
checkIO :: Type -> Infer Type
checkIO t = TyIO =.< runIO t
