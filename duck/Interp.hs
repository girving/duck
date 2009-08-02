{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | Duck interpreter

-- For now, this is dynamically typed

module Interp 
  ( prog
  , main
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup, intersect)
import qualified Data.List as List
import Data.Maybe
import Var
import Type
import Value
import SrcLoc
import Pretty
import qualified Lir
import Lir (Overload, Prog)
import qualified Prims
import qualified Data.Map as Map
import Util
import ExecMonad
import InferMonad hiding (withFrame)
import Control.Monad hiding (guard)
import Control.Monad.Trans
import qualified Infer

-- Environments

-- Some aliases for documentation purposes
type Globals = Env
type Locals = Env

lookup :: Prog -> Globals -> Locals -> SrcLoc -> Var -> Exec TValue
lookup prog global env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v global = return r -- fall back to global definitions
  | Just _ <- Map.lookup v (Lir.functions prog) = return (ValClosure v [], TyClosure [(v,[])]) -- if we find overloads, make a new closure
  | otherwise = execError loc ("unbound variable " ++ show v)

lookupConstructor :: Prog -> Var -> Exec (CVar, [Var], [TypeSet])
lookupConstructor prog c
  | Just tc <- Map.lookup c (Lir.conses prog)
  , Just (_,vl,cases) <- Map.lookup tc (Lir.datatypes prog)
  , Just tl <- Infer.lookupCons cases c = return (tc,vl,tl)
  | otherwise = execError noLoc ("unbound constructor " ++ show c)

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Lir.Prog -> Exec Globals
prog prog = foldM (statement prog) Map.empty (Lir.statements prog)

statement :: Prog -> Globals -> Lir.Statement -> Exec Globals
statement prog env (vl,e) = do
  d <- expr prog env Map.empty noLoc e
  dl <- case (vl,d) of
          ([_],_) -> return [d]
          (_, (ValCons c dl, TyCons c' tl)) | istuple c, c == c', length vl == length dl, length vl == length tl -> return $ zip dl tl
          _ -> execError noLoc ("expected "++show (length vl)++"-tuple, got "++show (pretty d))
  return $ foldl (\g (v,d) -> Map.insert v d g) env (zip (map unLoc vl) dl)

-- Perform a computation and then cast the result to a (more general) type.
-- For now, this cast is a nop on the data, but in future it may not be.
cast :: Prog -> Type -> Exec TValue -> Exec TValue
cast _ t x = do
  (d,_) <- x
  return (d,t)

expr :: Prog -> Globals -> Locals -> SrcLoc -> Lir.Exp -> Exec TValue
expr prog global env loc = exp where
  exp (Lir.Int i) = return $ (ValInt i, TyInt)
  exp (Lir.Var v) = lookup prog global env loc v
  exp (Lir.Apply e1 e2) = do
    v1 <- exp e1
    v2 <- exp e2
    apply prog global v1 v2 loc
  exp (Lir.Let v e body) = do
    d <- exp e
    expr prog global (Map.insert v d env) loc body
  exp ce@(Lir.Case e pl def) = do
    gt <- getGlobalTypes
    t <- liftInfer $ Infer.expr prog gt (Map.map snd env) loc ce
    d <- exp e
    case d of
      (ValCons c dl, TyCons tv types) -> do
        case find (\ (c',_,_) -> c == c') pl of
          Just (_,vl,e') ->
            if a == length dl then do
              (_, tvl, cases) <- liftInfer $ Infer.lookupDatatype prog loc tv
              let Just tl = Infer.lookupCons cases c
                  tenv = Map.fromList (zip tvl types)
                  tl' = map (substVoid tenv) tl
              cast prog t $ expr prog global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl (zip dl tl'))) loc e'
            else
              execError loc ("arity mismatch in pattern: "++show (pretty c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
                ++" but got ["++concat (intersperse "," (map (show . pretty) vl))++"]")
            where a = length vl
          Nothing -> case def of
            Nothing -> execError loc ("pattern match failed: exp = " ++ show (pretty d) ++ ", cases = " ++ show pl)
            Just (v,e') -> cast prog t $ expr prog global (Map.insert v d env) loc e' 
      _ -> execError loc ("expected block, got " ++ show (pretty d))
  exp (Lir.Cons c el) = do
    (args,types) <- unzip =.< mapM exp el
    (tv,vl,tl) <- lookupConstructor prog c
    result <- runMaybeT $ unifyList (applyTry prog) tl types
    case result of
      Just (tenv,[]) -> return (ValCons c args, TyCons tv targs) where
        targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
      _ -> execError loc (show (pretty c)++" expected arguments "++show (prettylist tl)++", got "++show (prettylist args)) 
  exp (Lir.Binop op e1 e2) = do
    (d1,t1) <- exp e1
    (d2,t2) <- exp e2
    d <- Prims.prim loc op d1 d2
    t <- liftInfer $ Prims.primType loc op t1 t2
    return (d,t)
  exp (Lir.Bind v e1 e2) = do
    d <- exp e1
    global <- getGlobalTypes
    t <- liftInfer $ Infer.expr prog global (Map.insert v (snd d) (Map.map snd env)) loc e2
    return (ValBindIO v d e2, t)
  exp (Lir.Return e) = do
    (d,t) <- exp e
    return (ValLiftIO d, TyIO t)
  exp (Lir.PrimIO p el) = do
    (dl,tl) <- unzip =.< mapM exp el
    t <- liftInfer $ Prims.primIOType loc p tl
    return (ValPrimIO p dl, TyIO t)
  exp (Lir.Spec e ts) = do
    (d,t) <- exp e
    result <- runMaybeT $ unify (applyTry prog) ts t
    case result of
      Just (tenv,[]) -> return (d,substVoid tenv ts)
      Nothing -> execError loc (show (pretty e)++" has type '"++show (pretty t)++"', which is incompatible with type specification '"++show (pretty ts))
      Just (_,leftovers) -> execError loc ("type specification '"++show (pretty ts)++"' is invalid; can't overload on contravariant "++showContravariantVars leftovers)
  exp (Lir.ExpLoc l e) = expr prog global env l e

apply :: Prog -> Globals -> TValue -> TValue -> SrcLoc -> Exec TValue
apply prog global (ValClosure f args, ft) v2 loc = do
  gt <- getGlobalTypes
  t <- liftInfer $ Infer.apply prog gt ft (snd v2) loc
  cast prog t $ apply' prog global f (args ++ [v2]) loc
apply _ _ v1 _ loc = execError loc ("expected a -> b, got " ++ show (pretty v1))

applyTry :: Prog -> Type -> Type -> MaybeT Exec Type
applyTry prog t1 t2 = do
  global <- lift getGlobalTypes
  mapMaybeT liftInfer (Infer.applyTry prog global t1 t2)

resolve :: Prog -> Var -> [Type] -> SrcLoc -> Exec (Maybe Overload)
resolve prog f args loc = do
  global <- getGlobalTypes
  liftInfer $ Infer.resolve prog global f args loc

-- Overloaded function application
apply' :: Prog -> Globals -> Var -> [TValue] -> SrcLoc -> Exec TValue
apply' prog global f args loc = do
  let types = map snd args
  overload <- resolve prog f types loc
  case overload of
    Nothing -> return (ValClosure f args, TyClosure [(f,types)])
    Just (_,_,vl,e) -> withFrame f args loc $ expr prog global (Map.fromList (zip vl args)) loc e

_typeof = typeof -- unused for now
typeof :: Prog -> Value -> Exec Type
typeof _ (ValInt _) = return TyInt
typeof prog (ValCons c args) = do
  tl <- mapM (typeof prog) args
  (tv, vl, tl') <- lookupConstructor prog c
  result <- runMaybeT $ unifyList (applyTry prog) tl' tl
  case result of
    Just (tenv,[]) -> return $ TyCons tv targs where
      targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
    _ -> execError noLoc ("failed to unify types "++show (prettylist tl)++" with "++show (prettylist tl'))
typeof _ (ValClosure _ _) = return $ TyFun TyVoid TyVoid
typeof _ (ValBindIO _ _ _) = return $ TyIO TyVoid
typeof _ (ValPrimIO _ _) = return $ TyIO TyVoid
typeof _ (ValLiftIO _) = return $ TyIO TyVoid

-- IO and main
main :: Prog -> Globals -> (GlobalTypes, FunctionInfo) -> IO ()
main prog global info = runExec info $ do
  main <- lookup prog global Map.empty noLoc (V "main")
  _ <- runIO prog global Map.empty main
  return ()

runIO :: Prog -> Globals -> Locals -> TValue -> Exec TValue
runIO _ _ _ (ValLiftIO d, TyIO t) = return (d,t)
runIO prog global _ (ValPrimIO Lir.TestAll [], TyIO t) = testAll prog global >.= \d -> (d,t)
runIO _ _ _ (ValPrimIO p args, TyIO t) = Prims.primIO p args >.= \d -> (d,t)
runIO prog global env (ValBindIO v m e, TyIO t) = do
  d <- runIO prog global env m
  let env' = Map.insert v d env
  d' <- expr prog global env' noLoc e
  cast prog t $ runIO prog global env' d'
runIO _ _ _ d =
  execError noLoc ("expected IO computation, got "++show (pretty d))

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
        success
    | otherwise = success
  nop = return $ ValCons (V "()") []

