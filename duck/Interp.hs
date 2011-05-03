{-# LANGUAGE PatternGuards, TypeSynonymInstances, ScopedTypeVariables #-}
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
import qualified Data.Set as Set
import Control.Monad hiding (guard)
import Control.Monad.Trans

import Util
import Var
import Type
import Prims
import Memory
import Value
import SrcLoc
import Pretty
import Lir
import ExecMonad
import qualified Infer
import qualified Base

-- Environments

-- Some aliases for documentation purposes
type Globals = Env
type Locals = Env
type LocalTypes = TypeEnv

lookup :: Globals -> Locals -> SrcLoc -> Var -> Exec Value
lookup global env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v global = return r -- fall back to global definitions
  | otherwise = getProg >>= lp where
  lp prog
    | Just _ <- Map.lookup v (progOverloads prog) = return (value $ ValClosure v [] []) -- if we find overloads, make a new closure
    | Just _ <- Map.lookup v (progFunctions prog) = return (value $ ValClosure v [] []) -- this should never be used
    | Just _ <- Map.lookup v (progDatatypes prog) = return valEmpty
    | otherwise = execError loc ("unbound variable" <+> quoted v)

-- | Pack up the free variables of an expression into a packed environment
packEnv :: LocalTypes -> Locals -> Exp -> [(Var, TypeVal, Value)]
packEnv tenv env e = map grab vl where
  vl = freeOf (Map.keysSet tenv) e
  grab v = (v, fromJust (Map.lookup v tenv), fromJust (Map.lookup v env))

unpackEnv :: [(Var, TypeVal, Value)] -> (LocalTypes, Locals)
unpackEnv penv = (tenv,env) where
  tenv = foldl (\e (v,t,_) -> Map.insert v t e) Map.empty penv
  env = foldl (\e (v,_,d) -> Map.insert v d e) Map.empty penv

-- |Process a list of definitions into the global environment.
prog :: Exec Globals
prog = getProg >>= foldM definition Map.empty . progDefinitions

definition :: Globals -> Definition -> Exec Globals
definition env d@(Def vl e) = withFrame (V $ intercalate "," $ map (var . unLoc) vl) [] [] (loc d) $ do
  d <- expr env Map.empty Map.empty noLoc e
  dl <- case (vl,d) of
          ([_],_) -> return [d]
          (_, dl) -> return (unsafeUnvalConsN (length vl) dl)
  return $ foldl (\g (v,d) -> Map.insert v d g) env (zip (map unLoc vl) dl)

-- |A placeholder for when implicit casts stop being nops on the data.
cast :: TypeVal -> Exec Value -> Exec Value
cast _ x = x

inferExpr :: LocalTypes -> SrcLoc -> Exp -> Exec TypeVal
inferExpr env loc e = do
  t <- liftInfer $ Infer.expr env loc e
  when (t == TyVoid) $ execError loc $ "refusing to evaluate" <+> quoted e <> ", result is Void"
  return t

expr :: Globals -> LocalTypes -> Locals -> SrcLoc -> Exp -> Exec Value
expr global tenv env loc = exp where
  exp (ExpVal _ v) = return v
  exp (ExpVar v) = lookup global env loc v
  exp (ExpApply e1 e2) = do
    t1 <- inferExpr tenv loc e1
    v1 <- exp e1
    applyExpr global tenv env loc t1 v1 e2
  exp (ExpLet v e body) = do
    t <- inferExpr tenv loc e
    d <- exp e
    expr global (Map.insert v t tenv) (Map.insert v d env) loc body
  exp (ExpCase _ [] Nothing) = execError loc ("pattern match failed: no cases")
  exp (ExpCase _ [] (Just body)) = exp body
  exp ce@(ExpCase v pl def) = do
    ct <- inferExpr tenv loc ce
    t <- liftInfer $ Infer.lookup tenv loc v
    conses <- liftInfer $ Infer.lookupDatatype loc t
    d <- lookup global env loc v
    let i = unsafeTag d
        c = unLoc $ fst $ conses !! i
    case find (\ (c',_,_) -> c == c') pl of
      Just (_,vl,e') -> do
        empty <- emptyType loc t
        let Just tl = Infer.lookupCons conses c
            dl = if empty then map (const valEmpty) vl
                 else unsafeUnvalConsN (length vl) d
        cast ct $ expr global (insertList tenv vl tl) (insertList env vl dl) loc e'
      Nothing -> case def of
        Nothing -> execError loc ("pattern match failed: exp =" <+> quoted (pretty (t,d)) <> ", cases =" <+> show pl) -- XXX data printed
        Just e' -> cast ct $ expr global tenv env loc e'
  exp (ExpCons _ c el) = valCons c =.< mapM exp el
  exp (ExpPrim op el) = Base.prim loc op =<< mapM exp el
  exp (ExpBind v e1 e2) = do
    t <- inferExpr tenv loc e1
    d <- exp e1
    let d' = unsafeUnvalue d :: IOValue
    return $ value $ ValBindIO v t d' e2 (packEnv (Map.delete v tenv) env e2)
  exp (ExpReturn e) = value . ValLiftIO =.< exp e
  exp se@(ExpSpec e _) = do
    t <- inferExpr tenv loc se
    cast t $ exp e
  exp (ExpLoc l e) = expr global tenv env l e

-- |Check if a type contains no information.
-- TODO: Move this elsewhere and cache
-- TODO: Check for infinite loops (e.g., data A a of B (A (A a)))
emptyType :: SrcLoc -> TypeVal -> Exec Bool
emptyType loc = empty Set.empty where
  empty seen t = if Set.member t seen then return True else empty' (Set.insert t seen) t
  empty' _ (TyCons c _) | c == datatypeInt = return False
                        | c == datatypeChar = return False
                        | c == datatypeIO = return False
                        | c == datatypeDelayed = return False
                        | c == datatypeType = return True
  empty' seen (TyCons d args) = case dataConses d of
    [] -> execError loc ("datatype" <+> quoted d <+> "has no constructors, so we don't know if it's empty or not")
    [(_,tl)] -> do
      let tenv = Map.fromList $ zip (dataTyVars d) args
      empties <- mapM (empty seen . substVoid tenv) tl
      return $ and empties
    (_:_:_) -> return False
  empty' _ (TyFun _) = return False
  empty' _ TyVoid = execError loc "Void is neither empty nor nonempty"

-- |Evaluate an argument acording to the given transform
transExpr :: Globals -> LocalTypes -> Locals -> SrcLoc -> Exp -> Trans -> Exec Value
transExpr global tenv env loc e NoTrans = expr global tenv env loc e
transExpr _ tenv env _ e Delayed = return $ value $ ValDelay e (packEnv tenv env e)

applyExpr :: Globals -> LocalTypes -> Locals -> SrcLoc -> TypeVal -> Value -> Exp -> Exec Value
applyExpr global tenv env loc ft f e =
  apply global loc ft f (transExpr global tenv env loc e)
    =<< liftInfer (Infer.expr tenv loc e)

-- Because of the delay mechanism, we pass in two things related to the argument
-- "a".  The first argument provides the argument itself, whose evaluation must
-- be delayed until we know the correct transform to apply.  The second type
-- "at" is the type of the value which was passed in, and is the type used for
-- type inference/overload resolution.
apply :: Globals -> SrcLoc -> TypeVal -> Value -> (Trans -> Exec Value) -> TypeVal -> Exec Value
apply global loc ft@(TyFun _) fun ae at = case unsafeUnvalue fun :: FunValue of
  ValClosure f types args -> do
    -- infer return type
    (tt, rt) <- liftInfer $ Infer.apply loc ft at
    when (rt == TyVoid) $ execError loc $ "cannot apply" <+> quoted ft <+> "to" <+> quoted at <> ", result is Void"
    -- lookup appropriate overload (parallels Infer.apply/resolve)
    let tl = types ++ [at]
    o <- maybe
      (execError loc ("unresolved overload:" <+> quoted (prettyap f tl)))
      return =<< liftInfer (Infer.lookupOver f tl)
    -- we throw away the type because we can reconstruct it later with argType
    let tt' = fst $ overArgs o !! length args
    --when (tt /= tt') $ execError loc "XXX"
    a <- ae tt'
    let dl = args ++ [a]
    case o of
      Over _ _ _ _ Nothing ->
        -- partially applied
        return $ value $ ValClosure f tl dl
      Over oloc tl' _ vl (Just e) -> do
        -- full function call (parallels Infer.cache)
        let tl = map snd tl'
        cast rt $ withFrame f tl dl loc $ expr global (Map.fromList $ zip vl tl) (Map.fromList $ zip vl dl) oloc e
  ValDelay e penv -> do
    (_, rt) <- liftInfer $ Infer.apply loc ft at
    when (rt == TyVoid) $ execError loc $ "cannot force" <+> quoted ft <> ", result is Void"
    let (tenv,env) = unpackEnv penv
    cast rt $ expr global tenv env loc e
apply _ loc t1 v1 e2 t2 = do
  r <- liftInfer $ Infer.isTypeType t1
  case r of
    Just _ -> return valEmpty
    Nothing -> e2 NoTrans >>= \v2 -> execError loc ("can't apply" <+> quoted (t1,v1) <+> "to" <+> quoted (t2,v2))

-- |IO and main
main :: Prog -> Globals -> IO ()
main prog global = runExec prog $ do
  main <- lookup global Map.empty noLoc (V "main")
  _ <- runIO global (unsafeUnvalue main :: IOValue)
  return ()

runIO :: Globals -> IOValue -> Exec Value
runIO _ (ValLiftIO d) = return d
runIO global (ValPrimIO TestAll []) = testAll global
runIO _ (ValPrimIO p args) = Base.runPrimIO p args
runIO global (ValBindIO v tm m e penv) = do
  d <- runIO global m
  t <- liftInfer $ Infer.runIO tm
  let (tenv,env) = unpackEnv penv
  d' <- expr global (Map.insert v t tenv) (Map.insert v d env) noLoc e
  runIO global (unsafeUnvalue d' :: IOValue)

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
        _ <- runIO global (unsafeUnvalue d :: IOValue)
        success
    | otherwise = success
  nop = return valEmpty

