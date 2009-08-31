{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | Duck interpreter

-- For now, this is dynamically typed

module Interp 
  ( prog
  , main
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad hiding (guard)
import Control.Monad.Trans

import Util
import Var
import Type
import Prims
import Value
import SrcLoc
import Pretty
import Lir hiding (prog)
import ExecMonad
import qualified Infer
import qualified Base

-- Environments

-- Some aliases for documentation purposes
type Globals = Env
type Locals = Env

lookup :: Globals -> Locals -> SrcLoc -> Var -> Exec TValue
lookup global env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v global = return r -- fall back to global definitions
  | otherwise = getProg >>= lp where
  lp prog
    | Just _ <- Map.lookup v (progOverloads prog) = return 
        (ValClosure v [] -- if we find overloads, make a new closure
        ,typeClosure v [])
    | Just _ <- Map.lookup v (progFunctions prog) = return
        (ValClosure v [] -- this should never be used
        ,typeClosure v [])
    | Just _ <- Map.lookup v (progDatatypes prog) = return (ValType, typeType (TyCons v []))
    | otherwise = execError loc ("unbound variable " ++ qshow v)

-- |Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Exec Globals
prog = getProg >>= foldM definition Map.empty . progDefinitions

definition :: Globals -> Definition -> Exec Globals
definition env d@(Def vl e) = withFrame (V $ intercalate "," $ map (unV . unLoc) vl) [] (loc d) $ do
  d <- expr env Map.empty noLoc e
  dl <- case (vl,d) of
          ([_],_) -> return [d]
          (_, (ValCons c dl, TyCons c' tl)) | isTuple c, c == c', length vl == length dl, length vl == length tl -> return $ zip dl tl
          _ -> execError noLoc ("expected "++show (length vl)++"-tuple, got "++qshow d)
  return $ foldl (\g (v,d) -> Map.insert v d g) env (zip (map unLoc vl) dl)

-- |Perform a computation and then cast the result to a (more general) type.
-- For now, this cast is a nop on the data, but in future it may not be.
cast :: Type -> Exec TValue -> Exec TValue
cast t x = do
  (d,_) <- x
  return (d,t)

--runInfer :: SrcLoc -> Infer Type -> Exec Type
runInfer l f = do
  t <- liftInfer f
  when (t == TyVoid) $ execError l "<<void>>"
  return t

inferExpr :: Locals -> SrcLoc -> Exp -> Exec Type
inferExpr env loc = runInfer loc . Infer.expr (Map.map snd env) loc

expr :: Globals -> Locals -> SrcLoc -> Exp -> Exec TValue
expr global env loc = exp where
  exp (Int i) = return $ (ValInt i, typeInt)
  exp (Chr i) = return $ (ValChr i, typeChr)
  exp (Var v) = lookup global env loc v
  exp (Apply e1 e2) = do
    v1 <- exp e1
    applyExpr global env loc v1 e2
  exp (Let v e body) = do
    d <- exp e
    expr global (Map.insert v d env) loc body
  exp (Case _ [] Nothing) = execError loc ("pattern match failed: no cases")
  exp (Case _ [] (Just body)) = exp body
  exp ce@(Case v pl def) = do
    t <- inferExpr env loc ce
    d <- lookup global env loc v
    (c,dl,conses) <- case d of
      (v, TyCons tv types) -> do
        conses <- liftInfer $ Infer.lookupDatatype loc tv types
        case (v,conses) of
          (ValCons c dl,_) -> return (c,dl,conses)
          (ValType,[(Loc _ c,tl)]) -> return (c,map (const ValType) tl,conses)
          _ -> execError loc ("expected block, got "++qshow v)
      _ -> execError loc ("expected block, got "++qshow d)
    case find (\ (c',_,_) -> c == c') pl of
      Just (_,vl,e') ->
        if a == length dl then do
          let Just tl = Infer.lookupCons conses c
          cast t $ expr global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl (zip dl tl))) loc e'
        else
          execError loc ("arity mismatch in pattern: "++qshow c++" expected "++show a++" argument"++(if a == 1 then "" else "s")
            ++" but got ["++intercalate "," (map pshow vl)++"]")
        where a = length vl
      Nothing -> case def of
        Nothing -> execError loc ("pattern match failed: exp = " ++ qshow d ++ ", cases = " ++ show pl) -- XXX data printed
        Just e' -> cast t $ expr global env loc e' 
  exp (Cons c el) = do
    (args,types) <- unzip =.< mapM exp el
    (,) (ValCons c args) =.< runInfer loc (Infer.cons loc c types)
  exp (Prim op el) = do
    (dl,tl) <- unzip =.< mapM exp el
    d <- Base.prim loc op dl
    t <- runInfer loc $ Base.primType loc op tl
    return (d,t)
  exp (Bind v e1 e2) = do
    d <- exp e1
    dt <- liftInfer $ Infer.runIO (snd d)
    t <- inferExpr (Map.insert v (undefined,dt) env) loc e2
    return (ValBindIO v d env e2, t)
  exp (Return e) = do
    (d,t) <- exp e
    return (ValLiftIO d, typeIO t)
  exp (PrimIO p el) = do
    (dl,tl) <- unzip =.< mapM exp el
    t <- liftInfer $ Base.primIOType loc p tl
    return (ValPrimIO p dl, typeIO t)
  exp (Spec e ts) =
    secondM (runInfer loc . Infer.spec loc ts e) =<< exp e
  exp (ExpLoc l e) = expr global env l e

-- |Evaluate an argument acording to the given transform
transExpr :: Globals -> Locals -> SrcLoc -> Exp -> Maybe Trans -> Exec Value
transExpr global env loc e Nothing = fst =.< expr global env loc e
transExpr _ env _ e (Just Delayed) = return $ ValDelay env e

applyExpr :: Globals -> Locals -> SrcLoc -> TValue -> Exp -> Exec TValue
applyExpr global env loc f e =
  apply global loc f (transExpr global env loc e)
    =<< inferExpr env loc e

-- Because of the delay mechanism, we pass in two things related to the argument
-- "a".  The first argument provides the argument itself, whose evaluation must
-- be delayed until we know the correct transform to apply.  The second type
-- "at" is the type of the value which was passed in, and is the type used for
-- type inference/overload resolution.
apply :: Globals -> SrcLoc -> TValue -> (Maybe Trans -> Exec Value) -> Type -> Exec TValue
apply global loc (ValClosure f args, ft) ae at = do
  -- infer return type
  rt <- runInfer loc $ Infer.apply loc ft at
  -- lookup appropriate overload (parallels Infer.apply/resolve)
  let atl = map snd args ++ [at]
  o <- maybe 
    (execError loc ("unresolved overload: " ++ pshow f ++ " " ++ pshowlist atl))
    return =<< liftInfer (Infer.lookupOver f atl)
  -- determine type transform for this argument, and evaluate
  let tt = map fst $ overArgs o
  -- we throw away the type because we can reconstruct it later with argType
  a <- ae (tt !! length args)
  let al = args ++ [(a,at)]
  case o of
    Over _ _ _ _ Nothing -> 
      -- partially applied
      return (ValClosure f al, rt)
    Over oloc tl _ vl (Just e) -> do
      -- full function call (parallels Infer.cache)
      let al' = zipWith (\(a,_) (_,t) -> (a,t)) al tl
      cast rt $ withFrame f al' loc $ expr global (Map.fromList (zip vl al')) oloc e
apply global loc (ValDelay env e, ta) _ _ | Just (_,t) <- isTypeArrow ta =
  cast t $ expr global env loc e
apply _ loc (_,t1) _ t2 | Just (TyCons c tl) <- isTypeType t1, Just t <- isTypeType t2 = do
  prog <- getProg
  if length tl < length (Infer.lookupVariances prog c) 
    then return (ValType, typeType (TyCons c (tl++[t])))
    else execError loc ("can't apply "++qshow t1++" to "++qshow t2++", "++qshow c++" is already fully applied")
apply _ loc (v1,t1) e2 t2 = e2 Nothing >>= \v2 -> execError loc ("can't apply '"++pshow v1++" :: "++pshow t1++"' to '"++pshow v2++" :: "++pshow t2++"'")

-- |IO and main
main :: Prog -> Globals -> IO ()
main prog global = runExec prog $ do
  main <- lookup global Map.empty noLoc (V "main")
  _ <- runIO global main
  return ()

runIO :: Globals -> TValue -> Exec TValue
runIO _ (ValLiftIO d, io) | Just t <- isTypeIO io = return (d,t)
runIO global (ValPrimIO TestAll [], io) | Just t <- isTypeIO io = testAll global >.= \d -> (d,t)
runIO _ (ValPrimIO p args, io) | Just t <- isTypeIO io = Base.primIO p args >.= \d -> (d,t)
runIO global (ValBindIO v m env e, io) | Just t <- isTypeIO io = do
  d <- runIO global m
  d' <- expr global (Map.insert v d env) noLoc e
  cast t $ runIO global d'
runIO _ d =
  execError noLoc ("expected IO computation, got "++qshow d)

testAll :: Globals -> Exec Value
testAll global = do
  liftIO $ puts "running unit tests..."
  mapM_ test (Map.toList global)
  liftIO $ puts "success!"
  nop
  where
  test (V v,d)
    | isPrefixOf "test_" v = do
        liftIO $ puts ("  "++v)
        runIO global d
        success
    | otherwise = success
  nop = return $ ValCons (V "()") []

