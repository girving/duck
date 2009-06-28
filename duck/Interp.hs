{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- Duck interpreter

-- For now, this is dynamically typed

module Interp 
  ( prog
  , main
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import qualified Data.List
import Data.Maybe
import Var
import Type
import Value
import Pretty
import qualified Lir
import Lir (Overload, Prog)
import qualified Prims
import qualified Data.Map as Map
import Util
import ExecMonad
import Control.Monad hiding (guard)
import Control.Monad.Trans

-- Environments

-- Some aliases for documentation purposes
type Globals = Env
type Locals = Env

lookup :: Prog -> Globals -> Locals -> Var -> Exec Value
lookup prog global env v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v global = return r -- fall back to global definitions
  | Just _ <- Map.lookup v (Lir.functions prog) = return $ ValClosure v [] -- if we find overloads, make a new closure
  | otherwise = execError ("unbound variable " ++ show v)

lookupOverloads :: Prog -> Var -> [Overload]
lookupOverloads prog v = Map.findWithDefault [] v (Lir.functions prog)

lookupConstructor :: Prog -> Var -> Exec (CVar, [Var], [Type])
lookupConstructor prog c
  | Just tc <- Map.lookup c (Lir.conses prog)
  , Just (vl,cases) <- Map.lookup tc (Lir.datatypes prog)
  , Just tl <- Data.List.lookup c cases = return (tc,vl,tl)
  | otherwise = execError ("unbound constructor " ++ show c)

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Lir.Prog -> Exec Globals
prog prog = foldM (statement prog) Map.empty (Lir.statements prog)

statement :: Prog -> Globals -> ([Var], Lir.Exp) -> Exec Globals
statement prog env (vl,e) = do
  d <- expr prog env Map.empty e
  dl <- case (vl,d) of
          ([_],_) -> return [d]
          (_, ValCons c dl) | istuple c, length vl == length dl -> return dl
          _ -> execError ("expected "++show (length vl)++"-tuple, got "++show (pretty d))
  return $ foldl (\g (v,d) -> Map.insert v d g) env (zip vl dl)

expr :: Prog -> Globals -> Locals -> Lir.Exp -> Exec Value
expr prog global env = exp where
  exp (Lir.Int i) = return $ ValInt i
  exp (Lir.Var v) = lookup prog global env v
  exp (Lir.Apply e1 e2) = do
    v1 <- exp e1
    v2 <- exp e2
    case v1 of
      ValClosure f args -> apply prog global f (args ++ [v2])
      _ -> execError ("expected a -> b, got " ++ show (pretty v1))
  exp (Lir.Let v e body) = do
    d <- exp e
    expr prog global (Map.insert v d env) body
  exp (Lir.Case e pl def) = do
    d <- exp e
    case d of
      ValCons c dl -> case find (\ (c',_,_) -> c == c') pl of
        Just (_,vl,e') ->
          if a == length dl then
            expr prog global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl dl)) e'
          else
            execError ("arity mismatch in pattern: "++show (pretty c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
              ++" but got ["++concat (intersperse "," (map (show . pretty) vl))++"]")
          where a = length vl
        Nothing -> case def of
          Nothing -> execError ("pattern match failed: exp = " ++ show (pretty d) ++ ", cases = " ++ show pl)
          Just (v,e') -> expr prog global (Map.insert v d env) e' 
      _ -> execError ("expected block, got " ++ show (pretty d))
  exp (Lir.Cons c el) = ValCons c =.< mapM exp el
  exp (Lir.Binop op e1 e2) = do
    d1 <- exp e1
    d2 <- exp e2
    Prims.prim op d1 d2
  exp (Lir.Bind v e1 e2) = do
    d <- exp e1
    return (ValBindIO v d e2)
  exp (Lir.Return e) = exp e >.= ValLiftIO
  exp (Lir.PrimIO p el) = mapM exp el >.= ValPrimIO p

-- Overloaded function application
apply :: Prog -> Globals -> Var -> [Value] -> Exec Value
apply prog global f args = do
  types <- mapM (typeof prog) args
  let call = unwords (map show (pretty f : map (guard 51) types))
      prune o@(tl,_,_,_) = case unifyList tl types of
        Just _ -> Just o
        Nothing -> Nothing
      overloads = catMaybes (map prune rawOverloads) -- prune those that don't match
      isSpecOf a b = isJust (unifyList b a)
      isMinimal (tl,_,_,_) = all (\ (tl',_,_,_) -> isSpecOf tl tl' || not (isSpecOf tl' tl)) overloads
      rawOverloads = lookupOverloads prog f -- look up possibilities
      options overs = concatMap (\ (tl,r,_,_) -> concat ("\n  " : intersperse " -> " (map (show . guard 2) (tl ++ [r])))) overs
  case filter isMinimal overloads of -- prune away overloads which are more general than some other overload
    [] -> execError (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition (\ (_,_,l,_) -> length l == length args) os of
      ([],_) -> return $ ValClosure f args -- all overloads are still partially applied
      ([(_,_,vl,e)],[]) -> withFrame f args $ -- exactly one fully applied option
        expr prog global (foldl (\env (v,d) -> Map.insert v d env) Map.empty (zip vl args)) e
      (fully@(_:_),partially@(_:_)) -> execError (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)
      (fully@(_:_:_),[]) -> execError (call++" is ambiguous, possibilities are"++options fully)

typeof :: Prog -> Value -> Exec Type
typeof _ (ValInt _) = return TyInt
typeof prog (ValCons c args) = do
  tl <- mapM (typeof prog) args
  (tv, vl, tl') <- lookupConstructor prog c
  case unifyList tl' tl of
    Just tenv -> return $ TyApply tv targs where
      targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
    Nothing -> execError ("failed to unify types "++showlist tl++" with "++showlist tl') where
      showlist = unwords . (map (show . guard 51))
typeof _ (ValClosure _ _) = return $ TyFun TyVoid TyVoid
typeof _ (ValBindIO _ _ _) = return $ TyIO TyVoid
typeof _ (ValPrimIO _ _) = return $ TyIO TyVoid
typeof _ (ValLiftIO _) = return $ TyIO TyVoid

-- IO and main
main :: Prog -> Globals -> IO ()
main prog global = runExec $ do
  main <- lookup prog global Map.empty (V "main")
  _ <- runIO prog global Map.empty main
  return ()

runIO :: Prog -> Globals -> Locals -> Value -> Exec Value
runIO _ _ _ (ValLiftIO d) = return d
runIO prog global _ (ValPrimIO Lir.TestAll []) = testAll prog global
runIO _ _ _ (ValPrimIO p args) = Prims.primIO p args
runIO prog global env (ValBindIO v m e) = do
  d <- runIO prog global env m
  let env' = Map.insert v d env
  d' <- expr prog global env' e
  runIO prog global env' d'
runIO _ _ _ d =
  execError ("expected IO computation, got "++show (pretty d))

testAll :: Prog -> Globals -> Exec Value
testAll prog global = do
  liftIO $ putStrLn "running unit tests..."
  mapM_ test (Map.toList global)
  liftIO $ putStrLn "success!"
  nop
  where
  test (V v,d)
    | isPrefixOf "test_" v = do
        liftIO $ putStrLn ("  "++v)
        runIO prog global Map.empty d
    | otherwise = nop
  nop = return $ ValCons (V "()") []
