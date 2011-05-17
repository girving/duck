{-# LANGUAGE PatternGuards, TypeSynonymInstances, ScopedTypeVariables #-}
-- | Duck interpreter

-- For now, this is dynamically typed

module Interp
  ( prog
  ) where

import Prelude hiding (lookup)

import Control.Monad hiding (guard)
import Data.List hiding (lookup)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Util
import Var
import Type
import Memory
import Value
import SrcLoc
import Pretty
import Lir hiding (Globals)
import ExecMonad
import qualified Infer
import qualified Base
import Prims

-- Environments

-- Some aliases for documentation purposes
type Globals = Env
type Locals = Env
type LocalTypes = TypeEnv

lookupGlobal :: Globals -> SrcLoc -> Var -> Exec Value
lookupGlobal global loc v = case Map.lookup v global of
  Just r -> return r
  Nothing -> execError loc ("unbound global variable" <+> quoted v)

-- | Pack up the free variables of an expression into a packed environment
packEnv :: InScopeSet -> LocalTypes -> Locals -> Exp -> [(Var, TypeVal, Value)]
packEnv s tenv env e = map grab (free s e) where
  grab v = (v, fromJust (Map.lookup v tenv), fromJust (Map.lookup v env))

unpackEnv :: [(Var, TypeVal, Value)] -> (LocalTypes, Locals)
unpackEnv penv = (tenv,env) where
  tenv = foldl' (\e (v,t,_) -> Map.insert v t e) Map.empty penv
  env = foldl' (\e (v,_,d) -> Map.insert v d e) Map.empty penv

-- |Process a list of definitions into the global environment.
prog :: Exec Globals
prog = getProg >>= foldM definition Map.empty . progDefinitions

definition :: Globals -> Definition -> Exec Globals
definition env d@(Def st vl e) = withFrame (V $ intercalate "," $ map (\(L _ (V s)) -> s) vl) [] [] (loc d) $ do
  d <- expr st env Map.empty Map.empty noLoc e
  dl <- case (vl,d) of
          ([_],_) -> return [d]
          (_, dl) -> return (unsafeUnvalConsN (length vl) dl)
  return $ foldl' (\g (v,d) -> insertVar v d g) env (zip (map unLoc vl) dl)

-- |A placeholder for when implicit casts stop being nops on the data.
cast :: TypeVal -> Exec Value -> Exec Value
cast _ x = x

inferExpr :: Bool -> LocalTypes -> SrcLoc -> Exp -> Exec TypeVal
inferExpr static env loc = liftInfer . Infer.expr static env loc

expr :: Bool -> Globals -> LocalTypes -> Locals -> SrcLoc -> Exp -> Exec Value
expr static global tenv env loc = exp where
  exp (ExpAtom a) = atom global env loc a
  exp (ExpApply e1 e2) = do
    t1 <- inferExpr static tenv loc e1
    v1 <- exp e1
    st <- liftInfer $ Infer.staticFunction t1
    t2 <- inferExpr (static || st) tenv loc e2
    apply static global loc t1 v1 (transExpr global tenv env loc e2) t2
  exp (ExpLet v e body) = do
    t <- inferExpr static tenv loc e
    d <- exp e
    expr static global (Map.insert v t tenv) (Map.insert v d env) loc body
  exp ce@(ExpCase a pl def) = do
    ct <- inferExpr static tenv loc ce
    t <- liftInfer $ Infer.atom static tenv loc a
    conses <- liftInfer $ Infer.lookupDatatype loc t
    d <- atom global env loc a
    let i = unsafeTag d
        c = unLoc $ fst $ conses !! i
    case find (\ (c',_,_) -> c == c') pl of
      Just (_,vl,e') -> do
        empty <- emptyType loc t
        let Just tl = Infer.lookupCons conses c
            dl = if empty then map (const valEmpty) vl
                 else unsafeUnvalConsN (length vl) d
        cast ct $ expr static global (insertVars tenv vl tl) (insertVars env vl dl) loc e'
      Nothing -> case def of
        Nothing -> execError loc ("pattern match failed: exp =" <+> quoted (pretty (t,d)) <> cases pl) where
          cases [] = ", no cases"
          cases pl = ", cases = "++show pl -- TODO: use pretty printing
        Just e' -> cast ct $ expr static global tenv env loc e'
  exp (ExpCons _ c el) = valCons c =.< mapM exp el
  exp (ExpPrim op el) = Base.prim loc op =<< mapM exp el
  exp se@(ExpSpec e _) = do
    t <- inferExpr static tenv loc se
    cast t $ exp e
  exp (ExpLoc l e) = expr static global tenv env l e

atom :: Globals -> Locals -> SrcLoc -> Atom -> Exec Value
atom _ _ _ (AtomVal _ v) = return v
atom _ env loc (AtomLocal v) = case Map.lookup v env of
  Just v -> return v
  Nothing -> execError loc ("internal error: unbound local variable" <+> quoted v)
atom global _ loc (AtomGlobal v) = lookupGlobal global loc v

-- |Check if a type contains no information.
-- TODO: Move this elsewhere and cache
-- TODO: Check for infinite loops (e.g., data A a of B (A (A a)))
emptyType :: SrcLoc -> TypeVal -> Exec Bool
emptyType loc = empty Set.empty where
  empty seen t = if Set.member t seen then return True else empty' (Set.insert t seen) t
  empty' seen (TyCons d args) = case dataInfo d of
    DataPrim s -> return $ s == 0
    DataAlgebraic [] -> execError loc ("datatype" <+> quoted d <+> "has no constructors, and thus is neither empty nor nonempty")
    DataAlgebraic [(_,tl)] -> do
      let tenv = Map.fromList $ zip (dataTyVars d) args
      empties <- mapM (empty seen . substVoid tenv) tl
      return $ and empties
    DataAlgebraic (_:_:_) -> return False
  empty' _ (TyFun _) = return False
  empty' seen (TyStatic t _) = empty seen t
  empty' _ TyVoid = execError loc "Void is neither empty nor nonempty"

-- |Evaluate an argument acording to the given transform
transExpr :: Globals -> LocalTypes -> Locals -> SrcLoc -> Exp -> Trans -> Exec Value
transExpr global tenv env loc e NoTrans = expr False global tenv env loc e
transExpr _ tenv env _ e Delay = return $ value $ ValDelay e (packEnv Set.empty tenv env e)
transExpr global tenv env loc e Static = expr True global tenv env loc e

-- Because of the delay mechanism, we pass in two things related to the argument
-- "a".  The first argument provides the argument itself, whose evaluation must
-- be delayed until we know the correct transform to apply.  The second type
-- "at" is the type of the value which was passed in, and is the type used for
-- type inference/overload resolution.
apply :: Bool -> Globals -> SrcLoc -> TypeVal -> Value -> (Trans -> Exec Value) -> TypeVal -> Exec Value
apply static global loc ft@(TyFun _) fun ae at 
  | ValClosure f types args <- unsafeUnvalue fun = do
    -- infer return type
    (tt, rt) <- liftInfer $ Infer.apply static loc ft at
    -- lookup appropriate overload (parallels Infer.apply/resolve)
    let tl = types ++ [if tt == Static then at else deStatic at]
    o <- maybe
      (execError loc $ "unresolved overload:" <+> quoted (prettyap f tl))
      return =<< liftInfer (Infer.lookupOver f tl)
    -- we throw away the type because we can reconstruct it later with argType
    a <- ae tt
    let dl = args ++ [a]
    case o of
      Over _ _ _ _ Nothing -> -- partially applied
        return $ value $ ValClosure f tl dl
      Over oloc tl' _ vl (Just e) -> do -- full function call (parallels Infer.cache)
        let tl = map transType tl'
        cast rt $ withFrame f tl dl loc $ expr static global (Map.fromList $ zip vl tl) (Map.fromList $ zip vl dl) oloc e
apply static global loc t1 v1 e2 t2 = 
  app Infer.isTypeType appty $
  app Infer.isTypeDelay appdel $
  e2 NoTrans >>= \v2 -> execError loc ("can't apply" <+> quoted (t1,v1) <+> "to" <+> quoted (t2,v2)) where
  app t f r = maybe r f =<< liftInfer (t t1)
  appty _ = return valEmpty
  appdel _ = do
    (_, rt) <- liftInfer $ Infer.apply static loc t1 t2
    let (tenv,env) = unpackEnv penv
    cast rt $ expr static global tenv env loc e
    where ValDelay e penv = unsafeUnvalue v1
