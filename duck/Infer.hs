{-# LANGUAGE PatternGuards, ScopedTypeVariables #-}
-- Duck type inference

module Infer
  ( prog
  , expr
  , apply
  , applyTry
  , resolve
  , lookupDatatype
  ) where

import Var
import Type
import Util
import Pretty
import Lir (Prog, Datatype, Overload)
import qualified Lir
import qualified Data.Map as Map
import Data.List hiding (lookup, intersect)
import qualified Data.List
import Control.Monad.Error hiding (guard, join)
import InferMonad
import Prelude hiding (lookup)
import qualified Prims
import Data.Maybe
import qualified Data.List as List
import Text.PrettyPrint

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
  | Just _ <- Map.lookup v (Lir.functions prog) = return $ TyClosure [(v,[])] -- if we find overloads, make a new closure
  | otherwise = typeError ("unbound variable " ++ show v)

lookupDatatype :: Prog -> CVar -> Infer Datatype
lookupDatatype prog tv
  | Just d <- Map.lookup tv (Lir.datatypes prog) = return d
  | otherwise = typeError ("unbound datatype constructor " ++ show tv)

lookupOverloads :: Prog -> Var -> Infer [Overload]
lookupOverloads prog f
  | Just o <- Map.lookup f (Lir.functions prog) = return o
  | otherwise = typeError ("unbound function " ++ show f)

lookupConstructor :: Prog -> Var -> Infer (CVar, [Var], [TypeSet])
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
          (_, TyCons c tl) | istuple c, length vl == length tl -> return tl
          _ -> typeError ("expected "++show (length vl)++"-tuple, got "++show (pretty t))
  return $ foldl (\g (v,t) -> Map.insert v t g) env (zip vl tl)

expr :: Prog -> Globals -> Locals -> Lir.Exp -> Infer Type
expr prog global env = exp where
  exp (Lir.Int _) = return TyInt
  exp (Lir.Var v) = lookup prog global env v
  exp (Lir.Apply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    apply prog global t1 t2
  exp (Lir.Let v e body) = do
    t <- exp e
    expr prog global (Map.insert v t env) body
  exp (Lir.Case e pl def) = do
    t <- exp e
    case t of
      TyVoid -> return TyVoid
      TyCons tv types -> do
        (tvl, cases) <- lookupDatatype prog tv
        let tenv = Map.fromList (zip tvl types)
            caseType (c,vl,e')
              | Just tl <- List.lookup c cases, a <- length tl =
                  if length vl == a then
                    let tl' = map (subst tenv) tl in
                    case mapM unsingleton tl' of
                      Nothing -> typeError ("datatype declaration "++show (pretty tv)++" is invalid, constructor "++show (pretty c)++" has nonconcrete types "++show (prettylist tl'))
                      Just tl -> expr prog global (foldl (\e (v,t) -> Map.insert v t e) env (zip vl tl)) e'
                  else
                    typeError ("arity mismatch in pattern: "++show (pretty c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
                      ++" but got ["++concat (intersperse ", " (map (show . pretty) vl))++"]")
              | otherwise = typeError ("datatype "++show (pretty tv)++" has no constructor "++show (pretty c))
            defaultType Nothing = return []
            defaultType (Just (v,e')) = expr prog global (Map.insert v t env) e' >.= \t -> [t]
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        joinList prog global (caseResults ++ defaultResults)
      _ -> typeError ("expected datatype, got "++show (pretty t))
  exp (Lir.Cons c el) = do
    args <- mapM exp el
    (tv,vl,tl) <- lookupConstructor prog c
    result <- runMaybeT $ unifyList (applyTry prog global) tl args
    case result of
      Just (tenv,[]) -> return $ TyCons tv targs where
        targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
      _ -> typeError (show (pretty c)++" expected arguments "++show (prettylist tl)++", got "++show (prettylist args))
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
  exp (Lir.ExpLoc _ e) = exp e -- TODO

join :: Prog -> Globals -> Type -> Type -> Infer Type
join prog global t1 t2 = do
  result <- runMaybeT $ intersect (applyTry prog global) t1 t2
  case result of
    Just t -> return t
    _ -> typeError ("failed to unify types "++show (pretty t1)++" and "++show (pretty t2))

-- In future, we might want this to produce more informative error messages
joinList :: Prog -> Globals -> [Type] -> Infer Type
joinList prog global = foldM1 (join prog global)

apply :: Prog -> Globals -> Type -> Type -> Infer Type
apply _ _ TyVoid _ = return TyVoid
apply _ _ _ TyVoid = return TyVoid
apply prog global (TyClosure fl) t2 = joinList prog global =<< mapM ap fl where
  ap :: (Var,[Type]) -> Infer Type
  ap (f,args) = do
    r <- lookupInfo f args'
    case r of
      Just t -> return t
      Nothing -> apply' prog global f args'
    where args' = args ++ [t2]
apply prog global (TyFun a r) t2 = do
  result <- runMaybeT $ unify'' (applyTry prog global) a t2
  case result of
    Just () -> return r
    _ -> typeError ("cannot apply "++show (pretty (TyFun a r))++" to "++show (pretty t2))
apply _ _ t1 _ = typeError ("expected a -> b, got " ++ show (pretty t1))

applyTry :: Prog -> Globals -> Type -> Type -> MaybeT Infer Type
applyTry prog global f t = catchError (lift $ apply prog global f t) (\_ -> nothing)

-- Resolve an overload.  A result of Nothing means all overloads are still partially applied.
resolve :: Prog -> Globals -> Var -> [Type] -> Infer (Maybe Overload)
resolve prog global f args = do
  rawOverloads <- lookupOverloads prog f -- look up possibilities
  let call = show (pretty f <+> prettylist args)
      prune o@(tl,_,_,_) = runMaybeT $ unifyList (applyTry prog global) tl args >. o
  overloads <- catMaybes =.< mapM prune rawOverloads -- prune those that don't match
  let isSpecOf :: [TypeSet] -> [TypeSet] -> Infer Bool
      isSpecOf a b = isJust =.< runMaybeT (unifyListSkolem (applyTry prog global) b a)
      isMinimal (tl,_,_,_) = allM (\ (tl',_,_,_) -> do
        less <- isSpecOf tl tl'
        more <- isSpecOf tl' tl
        return $ less || not more) overloads
      options overs = concatMap (\ (tl,r,_,_) -> "\n  "++show (pretty (foldr TsFun r tl))) overs
  filtered <- filterM isMinimal overloads -- prune away overloads which are more general than some other overload
  case filtered of
    [] -> typeError (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition (\ (_,_,l,_) -> length l == length args) os of
      ([],_) -> return Nothing -- all overloads are still partially applied
      ([o],[]) -> return (Just o) -- exactly one fully applied option
      (fully@(_:_),partially@(_:_)) -> typeError (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)
      (fully@(_:_:_),[]) -> typeError (call++" is ambiguous, possibilities are"++options fully)

-- Overloaded function application
apply' :: Prog -> Globals -> Var -> [Type] -> Infer Type
apply' prog global f args = do
  overload <- resolve prog global f args
  case overload of
    Nothing -> return $ TyClosure [(f,args)]
    Just o -> cache prog global f args o

-- Type infer a function call and cache the results
-- The overload is assumed to match, since this is handled by apply.
--
-- TODO: cache currently infers every nonvoid function call at least twice, regardless of recursion.  Fix this.
-- TODO: we should tweak this so that only intermediate (non-fixpoint) types are recorded into a separate map, so that
-- they can be easily rolled back in SFINAE cases _without_ rolling back complete computations that occurred in the process.
cache :: Prog -> Globals -> Var -> [Type] -> Overload -> Infer Type
cache prog global f args (types,r,vl,e) = do
  Just (tenv, leftovers) <- runMaybeT $ unifyList (applyTry prog global) types args
  let call = show (pretty f <+> prettylist args)
      vars = case contravariantVars leftovers of
        [v] -> "variable "++show (pretty v)
        vl -> "variables "++concat (intersperse ", " (map (show . pretty) vl))
  unless (null leftovers) $ typeError (call++" uses invalid overload "++show (pretty (foldr TsFun r types))++"; can't overload on contravariant "++vars)
  let tl = map (substVoid tenv) types
      rs = substVoid tenv r
      fix prev = do
        r' <- withFrame f tl (expr prog global (Map.fromList (zip vl tl)) e)
        result <- runMaybeT $ intersect (applyTry prog global) r' rs
        case result of
          Nothing -> typeError ("in call "++call++", failed to unify result "++show (pretty r')++" with return signature "++show (pretty rs))
          Just r -> do
            insertInfo f tl r
            if prev == r
              then return r
              else fix r
  insertInfo f tl TyVoid -- recursive function calls are initially assumed to be void
  fix TyVoid

-- This is the analog for Interp.runIO for types.  It exists by analogy even though it is very simple.
runIO :: Type -> Infer Type
runIO (TyIO t) = return t
runIO t = typeError ("expected IO type, got "++show (pretty t))

-- Verify that a type is in IO, and leave it unchanged if so
checkIO :: Type -> Infer Type
checkIO t = TyIO =.< runIO t
