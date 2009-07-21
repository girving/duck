{-# LANGUAGE PatternGuards #-}
-- | Duck Types

module Type
  ( Type(..)
  , TypeSet(..)
  , TypeEnv
  , unify
  , unify''
  , unifyList
  , unifyList''
  , unifyListSkolem
  , intersect
  , intersectList
  , subst
  , substVoid
  , occurs
  , singleton
  , unsingleton
  , contravariantVars
  ) where

import Var
import Pretty
import Text.PrettyPrint
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad hiding (guard)
import Control.Arrow hiding ((<+>))
import Util

-- |A concrete type (the types of values are always concrete)
data Type
  = TyCons CVar [Type]
  | TyClosure [(Var,[Type])] -- an intersection of one or more closures
  | TyFun Type Type
  | TyIO Type
  | TyInt
  | TyVoid
  deriving (Eq, Ord, Show)

-- |A set of concrete types (used for function overloads).  This is the same
-- as 'Type' except that it can contain type variables.
data TypeSet
  = TsVar Var
  | TsCons CVar [TypeSet]
  | TsClosure [(Var,[TypeSet])] -- an intersection of one or more closures
  | TsFun TypeSet TypeSet
  | TsIO TypeSet
  | TsInt
  | TsVoid
  deriving (Eq, Ord, Show)

type TypeEnv = Map Var Type

-- |The type of functions which say how to apply closure types to types
type Apply m = Type -> Type -> m Type

-- |Symmetric unify: @z <- intersect x y@ means that a value of type x or y
-- can be safely viewed as having type z.
--
-- The first argument says how to apply closure types to types.
intersect :: MonadMaybe m => Apply m -> Type -> Type -> m Type
intersect apply (TyCons c tl) (TyCons c' tl') | c == c' = TyCons c =.< intersectList apply tl tl'
intersect apply (TyFun s t) (TyFun s' t') = do
  ss <- union apply s s' -- note contravariance
  tt <- intersect apply t t' -- back to covariance
  return $ TyFun ss tt
intersect apply (TyFun s t) f@(TyClosure _) = do
  r <- apply f s
  t <- intersect apply t r
  return $ TyFun s t
intersect apply t@(TyClosure _) t'@(TyFun _ _) = intersect apply t' t
intersect _ (TyClosure f) (TyClosure f') = return (TyClosure (List.union f f'))
intersect apply (TyIO t) (TyIO t') = TyIO =.< intersect apply t t'
intersect _ TyInt TyInt = return TyInt
intersect _ TyVoid t = return t
intersect _ t TyVoid = return t
intersect _ _ _ = nothing

-- |The equivalent of 'intersect' for lists.  The two lists must have the same size.
intersectList :: MonadMaybe m => Apply m -> [Type] -> [Type] -> m [Type]
intersectList _ [] [] = return []
intersectList apply (t:tl) (t':tl') = do
  t'' <- intersect apply t t'
  tl'' <- intersectList apply tl tl'
  return (t'':tl'')
intersectList _ _ _ = nothing

-- |Symmetric antiunify: @z <- union x y@ means that a value of type z can be
-- safely viewed as having type x and type y.
union :: MonadMaybe m => Apply m -> Type -> Type -> m Type
union apply (TyCons c tl) (TyCons c' tl') | c == c' = TyCons c =.< unionList apply tl tl'
union apply (TyFun s t) (TyFun s' t') = do
  ss <- intersect apply s s' -- note contravariance
  tt <- union apply t t' -- back to covariance
  return $ TyFun ss tt
union apply (TyFun s t) f@(TyClosure _) = do
  r <- apply f s
  t <- union apply t r
  return $ TyFun s t
union apply t@(TyClosure _) t'@(TyFun _ _) = union apply t' t
union _ (TyClosure f) (TyClosure f') = return (TyClosure (List.union f f'))
union apply (TyIO t) (TyIO t') = TyIO =.< union apply t t'
union _ TyInt TyInt = return TyInt
union _ TyVoid _ = return TyVoid
union _ _ TyVoid = return TyVoid
union _ _ _ = nothing

-- |The equivalent of 'union' for lists.  The two lists must have the same size.
unionList :: MonadMaybe m => (Type -> Type -> m Type) -> [Type] -> [Type] -> m [Type]
unionList _ [] [] = return []
unionList apply (t:tl) (t':tl') = do
  t'' <- union apply t t'
  tl'' <- unionList apply tl tl'
  return (t'':tl'')
unionList _ _ _ = nothing

-- |Directed unify: @unify s t@ tries to turn @s@ into @t@ via variable substitutions,
-- but not the other way round.
--
-- Note that the occurs check is unnecessary here due to directedness.  In
-- particular, all TypeEnv bindings are of the form v -> t, where t is a Type.
-- Since Type contains no type variables, the occurs check succeeds trivially.
--
-- Operationally, @unify x y@ answers the question "If a function takes an
-- argument of type x, can we pass it a y?"  As an example, @unify x Void@ always
-- succeeds since the hypothesis is vacuously true: there are no values of
-- type Void.
--
-- The order in which subtypes are unified must be adaptive in the presence of
-- function type sets.  For example, when unifying (a -> Int, a) with
-- (Negate, Int), the value of "a" must be determined from the second part of
-- the tuple before the function part can be checked.  To handle this, unify'
-- produces a list of indeterminate subcomputations as it runs, and unify
-- iterates on this until a fixed point is reached.
unify :: MonadMaybe m => Apply m -> TypeSet -> Type -> m (TypeEnv, Leftovers)
unify apply t t' = unifyFix apply Map.empty =<< unify' apply Map.empty t t'

type Leftover = (TypeSet, Type)
type Leftovers = [Leftover]

unifyFix :: MonadMaybe m => Apply m -> TypeEnv -> (TypeEnv, Leftovers) -> m (TypeEnv, Leftovers)
unifyFix _ _ r@(_, []) = return r -- finished leftovers, so done
unifyFix _ prev r@(env, _) | prev == env = return r -- reached fixpoint without exhausing leftovers
unifyFix apply _ (env, leftovers) = unifyFix apply env =<< foldM step (env, []) leftovers where
  step (env, leftovers) (t,t') = do
    (env, l) <- unify' apply env t t'
    return (env, l ++ leftovers)

unify' :: MonadMaybe m => Apply m -> TypeEnv -> TypeSet -> Type -> m (TypeEnv, Leftovers)
unify' apply env (TsVar v) t =
  case Map.lookup v env of
    Nothing -> return (Map.insert v t env, [])
    Just t' -> intersect apply t t' >.= \t'' -> (Map.insert v t'' env, [])
unify' apply env (TsCons c tl) (TyCons c' tl') | c == c' = unifyList' apply env tl tl'
unify' apply env f@(TsFun s t) f'@(TyFun s' t') = do
  case unsingleton' env s of
    Nothing -> return (env,[(f,f')])
    Just s -> do
      unify'' apply s' s -- note reversed arguments due to contravariance
      unify' apply env t t' -- back to covariance
unify' apply env f@(TsFun s t) f'@(TyClosure _) = do
  case unsingleton' env s of
    Nothing -> return (env,[(f,f')])
    Just s -> do
      t' <- apply f' s
      unify' apply env t t'
unify' _ env (TsClosure f) (TyClosure f') = -- succeed if f' is a subset of f
  if all (\x -> List.elem (second (map singleton) x) f) f' then return (env,[]) else nothing
unify' _ _ (TsClosure _) (TyFun _ _) = nothing -- TyFun is never considered as general as TyClosure
unify' apply env (TsIO t) (TyIO t') = unify' apply env t t'
unify' _ env TsInt TyInt = return (env,[])
unify' _ env _ TyVoid = return (env,[])
unify' _ _ _ _ = nothing

-- |Same as 'unify'', but the first argument is a type
unify'' :: MonadMaybe m => Apply m -> Type -> Type -> m ()
unify'' apply (TyCons c tl) (TyCons c' tl') | c == c' = unifyList'' apply tl tl'
unify'' apply (TyFun s t) (TyFun s' t') = do
  unify'' apply s' s -- contravariant
  unify'' apply t t' -- covariant
unify'' apply (TyFun s t) f@(TyClosure _) = do
  t' <- apply f s
  unify'' apply t t'
unify'' _ (TyClosure f) (TyClosure f') = -- succeed if f' is a subset of f
  if all (\x -> List.elem x f) f' then success else nothing
unify'' _ (TyClosure _) (TyFun _ _) = nothing -- TyFun is never considered as general as TyClosure
unify'' apply (TyIO t) (TyIO t') = unify'' apply t t'
unify'' _ TyInt TyInt = success
unify'' _ _ TyVoid = success
unify'' _ _ _ = nothing

-- |The equivalent of 'unify' for lists.  To succeed, the first argument must be
-- at least as long as the second argument (think of the first argument as the
-- types a function takes as arguments, and the second as the types of the
-- values it is passed).
unifyList :: MonadMaybe m => Apply m -> [TypeSet] -> [Type] -> m (TypeEnv, Leftovers)
unifyList apply tl tl' = unifyFix apply Map.empty =<< unifyList' apply Map.empty tl tl'

unifyList' :: MonadMaybe m => Apply m -> TypeEnv -> [TypeSet] -> [Type] -> m (TypeEnv, Leftovers)
unifyList' _ env _ [] = return (env,[])
unifyList' apply env (t:tl) (t':tl') = do
  (env,l1) <- unify' apply env t t'
  (env,l2) <- unifyList' apply env tl tl'
  return (env, l1 ++ l2)
unifyList' _ _ _ _ = nothing

-- |Same as 'unifyList'', but for Type instead of TypeSet
unifyList'' :: MonadMaybe m => Apply m -> [Type] -> [Type] -> m ()
unifyList'' _ _ [] = success
unifyList'' apply (t:tl) (t':tl') = do
  unify'' apply t t'
  unifyList'' apply tl tl'
unifyList'' _ _ _ = nothing

-- |'unifyList' for the case of two type sets.  Here the two sets of variables are
-- considered to come from separate namespaces.  To make this clear, we implement
-- this function using skolemization, by turning all variables in the second
-- TypeEnv into TyConses.
unifyListSkolem :: MonadMaybe m => Apply m -> [TypeSet] -> [TypeSet] -> m ()
unifyListSkolem apply x y = unifyList apply x (map skolemize y) >. ()

-- |Type environment substitution
subst :: TypeEnv -> TypeSet -> TypeSet
subst env (TsVar v)
  | Just t <- Map.lookup v env = singleton t
  | otherwise = TsVar v
subst env (TsCons c tl) = TsCons c (map (subst env) tl)
subst env (TsClosure fl) = TsClosure (map (second (map (subst env))) fl)
subst env (TsFun t1 t2) = TsFun (subst env t1) (subst env t2)
subst env (TsIO t) = TsIO (subst env t)
subst _ TsInt = TsInt
subst _ TsVoid = TsVoid

-- |Type environment substitution with unbound type variables defaulting to void
substVoid :: TypeEnv -> TypeSet -> Type
substVoid env (TsVar v) = Map.findWithDefault TyVoid v env
substVoid env (TsCons c tl) = TyCons c (map (substVoid env) tl)
substVoid env (TsClosure fl) = TyClosure (map (second (map (substVoid env))) fl)
substVoid env (TsFun t1 t2) = TyFun (substVoid env t1) (substVoid env t2)
substVoid env (TsIO t) = TyIO (substVoid env t)
substVoid _ TsInt = TyInt
substVoid _ TsVoid = TyVoid

-- |Occurs check
occurs :: TypeEnv -> Var -> TypeSet -> Bool
occurs env v (TsVar v') | Just t <- Map.lookup v' env = occurs' v t
occurs _ v (TsVar v') = v == v'
occurs env v (TsCons _ tl) = any (occurs env v) tl
occurs env v (TsClosure fl) = any (any (occurs env v) . snd) fl
occurs env v (TsFun t1 t2) = occurs env v t1 || occurs env v t2
occurs env v (TsIO t) = occurs env v t
occurs _ _ TsInt = False
occurs _ _ TsVoid = False

-- |Types contains no variables
occurs' :: Var -> Type -> Bool
occurs' _ _ = False

-- |This way is easy
singleton :: Type -> TypeSet
singleton (TyCons c tl) = TsCons c (map singleton tl)
singleton (TyClosure fl) = TsClosure (map (second (map singleton)) fl)
singleton (TyFun s t) = TsFun (singleton s) (singleton t)
singleton (TyIO t) = TsIO (singleton t)
singleton TyInt = TsInt
singleton TyVoid = TsVoid
 
-- |Convert a singleton typeset to a type if possible
unsingleton :: TypeSet -> Maybe Type
unsingleton = unsingleton' Map.empty

unsingleton' :: TypeEnv -> TypeSet -> Maybe Type
unsingleton' env (TsVar v) | Just t <- Map.lookup v env = return t
unsingleton' _ (TsVar _) = nothing
unsingleton' env (TsCons c tl) = TyCons c =.< mapM (unsingleton' env) tl
unsingleton' env (TsClosure fl) = TyClosure =.< mapM (secondM (mapM (unsingleton' env))) fl
unsingleton' env (TsFun s t) = do
  s <- unsingleton' env s
  t <- unsingleton' env t
  return $ TyFun s t
unsingleton' env (TsIO t) = TyIO =.< unsingleton' env t
unsingleton' _ TsInt = return TyInt
unsingleton' _ TsVoid = return TyVoid

-- TODO: I'm being extremely cavalier here and pretending that the space of
-- variables in TsCons and TsVar is disjoint.  When this fails in the future,
-- skolemize will need to be fixed to turn TsVar variables into fresh TyCons
-- variables.
skolemize :: TypeSet -> Type
skolemize (TsVar v) = TyCons v [] -- skolemization
skolemize (TsCons c tl) = TyCons c (map skolemize tl)
skolemize (TsClosure fl) = TyClosure (map (second (map skolemize)) fl)
skolemize (TsFun t1 t2) = TyFun (skolemize t1) (skolemize t2)
skolemize (TsIO t) = TyIO (skolemize t)
skolemize TsInt = TyInt
skolemize TsVoid = TyVoid

-- |If leftovers remain after unification, this function explains which
-- variables caused the problem.
contravariantVars :: Leftovers -> [Var]
contravariantVars = concatMap cv where
  cv (TsFun s _, _) = vars s
  cv _ = []
  vars (TsVar v) = [v]
  vars (TsCons _ tl) = concatMap vars tl
  vars (TsClosure fl) = concatMap (concatMap vars . snd) fl
  vars (TsFun t1 t2) = vars t1 ++ vars t2
  vars (TsIO t) = vars t
  vars TsInt = []
  vars TsVoid = []
 
-- Pretty printing

instance Pretty TypeSet where
  pretty' (TsVar v) = pretty' v
  pretty' (TsCons t []) = pretty' t
  pretty' (TsClosure [(f,[])]) = pretty' f
  pretty' (TsCons t tl) | istuple t = (2, hcat $ List.intersperse (text ", ") $ map (guard 3) tl)
  pretty' (TsCons t tl) = (50, guard 50 t <+> prettylist tl)
  pretty' (TsClosure fl) = (50, hsep (List.intersperse (text "&") (map (\ (f,tl) -> guard 50 f <+> prettylist tl) fl)))
  pretty' (TsFun t1 t2) = (1, guard 2 t1 <+> text "->" <+> guard 1 t2)
  pretty' (TsIO t) = (1, text "IO" <+> guard 2 t)
  pretty' TsInt = (100, text "Int")
  pretty' TsVoid = (100, text "Void")

instance Pretty Type where
  pretty' = pretty' . singleton
