{-# LANGUAGE PatternGuards #-}
-- Duck Types

module Type
  ( Type(..)
  , TypeEnv
  , unify
  , unifyList
  , unifyS
  , unifySList
  , subst
  , isConcrete
  ) where

import Var
import Pretty
import Text.PrettyPrint
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow hiding ((<+>))
import Util

data Type
  = TyVar Var
  | TyCons CVar [Type]
  | TyClosure Var [Type]
  | TyFun Type Type
  | TyIO Type
  | TyInt
  | TyVoid
  deriving (Eq, Ord, Show)

type TypeEnv = Map Var Type

-- Symmetric unify: unifyS x y = Just z means that a value of type x or y
-- can be safely viewed as having type z.
--
-- As with unify below, unifyS treats all function types as the same.
unifyS :: Type -> Type -> Maybe (TypeEnv, Type)
unifyS = unifyS' Map.empty

unifyS' :: TypeEnv -> Type -> Type -> Maybe (TypeEnv, Type)
unifyS' env (TyVar v) t' | Just t <- Map.lookup v env = unifyS' env t t'
unifyS' env t' (TyVar v) | Just t <- Map.lookup v env = unifyS' env t' t
unifyS' env t@(TyVar v) (TyVar v') | v == v' = Just (env,t)
unifyS' env (TyVar v) t | not (occurs env v t) = Just (Map.insert v t env, t)
unifyS' env t (TyVar v) | not (occurs env v t) = Just (Map.insert v t env, t)
unifyS' env (TyCons c tl) (TyCons c' tl') | c == c' = second (TyCons c) =.< unifySList' env tl tl'
unifyS' env t@(TyFun _ _) (TyFun _ _) = Just (env,t)
unifyS' env t@(TyFun _ _) (TyClosure _ _) = Just (env,t)
unifyS' env t@(TyClosure _ _) (TyFun _ _) = Just (env,t)
unifyS' env t@(TyClosure _ _) (TyClosure _ _) = Just (env,t)
unifyS' env (TyIO t) (TyIO t') = second TyIO =.< unifyS' env t t'
unifyS' env TyInt TyInt = Just (env,TyInt)
unifyS' env TyVoid t = Just (env,t)
unifyS' env t TyVoid = Just (env,t)
unifyS' _ _ _ = Nothing

-- The equivalent of unifyS for lists.  The two lists must have the same size.
unifySList :: [Type] -> [Type] -> Maybe (TypeEnv, [Type])
unifySList = unifySList' Map.empty

unifySList' :: TypeEnv -> [Type] -> [Type] -> Maybe (TypeEnv, [Type])
unifySList' env [] [] = Just (env,[])
unifySList' env (t:tl) (t':tl') = do
  (env,t'') <- unifyS' env t t'
  (env,tl'') <- unifySList' env tl tl'
  return (env, t'' : tl'')
unifySList' _ _ _ = Nothing

-- Directed unify: unify s t tries to turn s into t via variable substitutions,
-- but not the other way round.  Notes:
--   1. I've left out the occurs check for now, since at least in trivial cases
--      the directness avoids it.  I expect this will bite me later, at which
--      point I'll fix it.
--   2. unify treats all function types as the same, since my first use of this
--      is for overload resolution, and you can't overload on a function type.
--      Again, I'll probably have to fix this later.
--
-- Operationally, unify x y answers the question "If a function takes an
-- argument of type x, can we pass it a y?"  As an example, unify x Void always
-- succeeds since the hypothesis is vacuously true: there are no values of
-- type Void.
unify :: Type -> Type -> Maybe TypeEnv
unify = unify' Map.empty

unify' :: TypeEnv -> Type -> Type -> Maybe TypeEnv
unify' env (TyVar v) t =
  case Map.lookup v env of
    Nothing -> Just (Map.insert v t env)
    Just t' -> unifyS t t' >.= \ (_,t'') -> Map.insert v t'' env
unify' env (TyCons c tl) (TyCons c' tl') | c == c' = unifyList' env tl tl'
unify' env (TyFun _ _) (TyFun _ _) = Just env
unify' env (TyFun _ _) (TyClosure _ _) = Just env
unify' env (TyClosure _ _) (TyFun _ _) = Just env
unify' env (TyClosure _ _) (TyClosure _ _) = Just env
unify' env (TyIO t) (TyIO t') = unify' env t t'
unify' env TyInt TyInt = Just env
unify' env _ TyVoid = Just env
unify' _ _ _ = Nothing

-- The equivalent of unify for lists.  To succeed, the first argument must be
-- at least as long as the second argument (think of the first argument as the
-- types a function takes as arguments, and the second as the types of the
-- values it is passed).
unifyList :: [Type] -> [Type] -> Maybe TypeEnv
unifyList = unifyList' Map.empty

unifyList' :: TypeEnv -> [Type] -> [Type] -> Maybe TypeEnv
unifyList' env _ [] = Just env
unifyList' env (t:tl) (t':tl') = do
  env' <- unify' env t t'
  unifyList' env' tl tl'
unifyList' _ _ _ = Nothing

-- Type environment substitution
subst :: TypeEnv -> Type -> Type
subst env t@(TyVar v) = Map.findWithDefault t v env
subst env (TyCons c tl) = TyCons c (map (subst env) tl)
subst env (TyClosure c tl) = TyClosure c (map (subst env) tl)
subst env (TyFun t1 t2) = TyFun (subst env t1) (subst env t2)
subst env (TyIO t) = TyIO (subst env t)
subst _ TyInt = TyInt
subst _ TyVoid = TyVoid

-- Occurs check
occurs :: TypeEnv -> Var -> Type -> Bool
occurs env v (TyVar v') | Just t <- Map.lookup v' env = occurs env v t
occurs _ v (TyVar v') = v == v'
occurs env v (TyCons _ tl) = any (occurs env v) tl
occurs env v (TyClosure _ tl) = any (occurs env v) tl
occurs env v (TyFun t1 t2) = occurs env v t1 || occurs env v t2
occurs env v (TyIO t) = occurs env v t
occurs _ _ TyInt = False
occurs _ _ TyVoid = False

-- Check if a type contains any variables
-- For now, this doesn't recurse into function types
isConcrete :: Type -> Bool
isConcrete (TyVar _) = False
isConcrete (TyCons _ tl) = all isConcrete tl
isConcrete (TyClosure _ tl) = all isConcrete tl
isConcrete (TyFun _ _) = True
isConcrete (TyIO t) = isConcrete t
isConcrete TyInt = True
isConcrete TyVoid = True

-- Pretty printing

instance Pretty Type where
  pretty' (TyVar v) = pretty' v
  pretty' (TyCons t []) = pretty' t
  pretty' (TyClosure t []) = pretty' t
  pretty' (TyCons t tl) | istuple t = (2, hcat $ intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TyCons (V "[]") [t]) = (100, brackets (pretty t))
  pretty' (TyCons t tl) = (50, guard 50 t <+> prettylist tl)
  pretty' (TyClosure t tl) = (50, guard 50 t <+> prettylist tl)
  pretty' (TyFun t1 t2) = (1, guard 2 t1 <+> text "->" <+> guard 1 t2)
  pretty' (TyIO t) = (1, text "IO" <+> guard 2 t)
  pretty' TyInt = (100, text "Int")
  pretty' TyVoid = (100, text "Void")
