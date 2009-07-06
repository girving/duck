-- | Duck Types

module Type 
  ( Type(..)
  , unifyList
  ) where

import Var
import Pretty
import Text.PrettyPrint
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Util

data Type
  = TyVar Var
  | TyApply CVar [Type]
  | TyFun Type Type
  | TyIO Type
  | TyInt
  | TyVoid
  deriving (Eq, Ord, Show)

type TypeEnv = Map Var Type

-- |Symmetric unify: @unifyS x y = Just z@ means that a value of type x or y
-- can be safely viewed as having type z.
--
-- As with unify below, unifyS treats all function types as the same.
unifyS :: Type -> Type -> Maybe Type
unifyS t@(TyVar v) (TyVar v') | v == v' = Just t
unifyS (TyApply c tl) (TyApply c' tl') | c == c' = TyApply c =.< unifySList tl tl'
unifyS t@(TyFun _ _) (TyFun _ _) = Just t
unifyS t@(TyIO _) (TyIO _) = Just t
unifyS TyInt TyInt = Just TyInt
unifyS TyVoid t = Just t
unifyS t TyVoid = Just t
unifyS _ _ = Nothing

-- |The equivalent of 'unifyS' for lists.  The two lists must have the same size.
unifySList :: [Type] -> [Type] -> Maybe [Type]
unifySList [] [] = Just []
unifySList (t:tl) (t':tl') = do
  t'' <- unifyS t t'
  tl'' <- unifySList tl tl'
  return $ t'' : tl''
unifySList _ _ = Nothing

-- |Directed unify: @unify s t@ tries to turn @s@ into @t@ via variable substitutions,
-- but not the other way round.  Notes:
--
--   1. I've left out the occurs check for now, since at least in trivial cases
--      the directness avoids it.  I expect this will bite me later, at which
--      point I'll fix it.
--
--   2. unify treats all function types as the same, since my first use of this
--      is for overload resolution, and you can't overload on a function type.
--      Again, I'll probably have to fix this later.
--
--   3. IO types are similarly collapsed: you can't overload based on what
--      inside IO either.
--
-- Operationally, @unify x y@ answers the question "If a function takes an
-- argument of type x, can we pass it a y?"  As an example, @unify x Void@ always
-- succeeds since the hypothesis is vacuously true: there are no values of
-- type Void.
_unify :: Type -> Type -> Maybe TypeEnv
_unify = unify' Map.empty

unify' :: TypeEnv -> Type -> Type -> Maybe TypeEnv
unify' env (TyVar v) t = 
  case Map.lookup v env of
    Nothing -> Just (Map.insert v t env)
    Just t' -> unifyS t t' >.= \t'' -> Map.insert v t'' env
unify' env (TyApply c tl) (TyApply c' tl') | c == c' = unifyList' env tl tl'
unify' env (TyFun _ _) (TyFun _ _) = Just env
unify' env (TyIO _) (TyIO _) = Just env
unify' env TyInt TyInt = Just env
unify' env _ TyVoid = Just env
unify' _ _ _ = Nothing

-- |The equivalent of 'unify' for lists.  To succeed, the first argument must be
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

-- Pretty printing

instance Pretty Type where
  pretty' (TyVar v) = pretty' v
  pretty' (TyApply t tl) | istuple t = (2, hcat $ intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TyApply (V "[]") [t]) = (100, brackets (pretty t))
  pretty' (TyApply t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
  pretty' (TyFun t1 t2) = (1, guard 2 t1 <+> text "->" <+> guard 1 t2)
  pretty' (TyIO t) = (1, text "IO" <+> guard 2 t)
  pretty' TyInt = (100, text "Int")
  pretty' TyVoid = (100, text "Void")
