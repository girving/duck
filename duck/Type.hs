-- Duck Types

module Type where

import Var
import Pretty
import Text.PrettyPrint
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

data Type
  = TyVar Var
  | TyApply CVar [Type]
  | TyFun Type Type
  | TyInt
  | TyVoid
  deriving Show

type TypeEnv = Map Var Type

-- Directed unify: unify s t tries to turn s into t via variable substitutions,
-- but not the other way round.  Notes:
--   1. I've left out the occurs check for now, since at least in trivial cases
--      the directness avoids it.  I expect this will bite me later, at which
--      point I'll fix it.
--   2. unify treats all function types as the same, since my first use of this
--      is for overload resolution, and you can't overload on a function type.
--      Again, I'll probably have to fix this later.
unify :: Type -> Type -> Maybe TypeEnv
unify = unify' Map.empty

unify' :: TypeEnv -> Type -> Type -> Maybe TypeEnv
unify' env (TyVar v) t = Just (Map.insert v t env)
unify' env (TyApply c tl) (TyApply c' tl') | c == c' = unifyList' env tl tl'
unify' env (TyFun _ _) (TyFun _ _) = Just env
unify' env TyInt TyInt = Just env
unify' env TyVoid _ = Just env
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

-- Pretty printing

instance Pretty Type where
  pretty' (TyVar v) = pretty' v
  pretty' (TyApply t tl) | istuple t = (2, hcat $ intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TyApply t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
  pretty' (TyFun t1 t2) = (1, guard 2 t1 <+> text "->" <+> guard 1 t2)
  pretty' TyInt = (100, text "Int")
  pretty' TyVoid = (100, text "Void")
