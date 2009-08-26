{-# LANGUAGE PatternGuards, FlexibleInstances, ScopedTypeVariables, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, TypeSynonymInstances #-}
-- | Duck Types

module Type
  ( Type(..)
  , TypeSet(..)
  , TypeFun(..)
  , TypeInfo(..)
  , Variance(..)
  , TypeEnv
  , subset
  , subset''
  , subsetList
  , subsetList''
  , specializationList
  , union
  , subst
  , substVoid
  , occurs
  , singleton
  , unsingleton
  , freeVars
  , contravariantVars
  , showContravariantVars
  ) where

-- Explanation of covariance and contravariance:
--
-- You should think of a type as being the set of values that inhabit the type.
-- For example, the type Int is {0, 1, -1, 2, -2, ...}, and the type Void is
-- the empty set {}.  Subtype means subset, so Void is a subtype of all types.
-- In some of comments below, we'll use S(t) to denote this set of values.
--
-- The set logic is also useful for remembering what union and intersect do.
-- For example, (if c then a else b :: union A B) if (a :: A) and (b :: B),
-- since the set of values resulting from the "if" is the union of the sets of
-- values resulting from the two branches.  Intersection arises as the
-- contravariant version of union:
--
--     union (a -> t) (b -> t) = intersect a b -> t
--
-- Note that Void is equivalent to the Haskell type forall a. a.  On the other
-- side of the lattice, the type Top corresponding to the type exists a. a would
-- be the type that could be anything.
--
-- A concrete example: the empty list [] has type List Void.  If we start adding
-- values to the list to get [a], [a,b], etc. the type gets larger and larger
-- as we union together more and more types.

import Var
import Pretty
import Data.Maybe
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad hiding (guard)
import Util

-- |The type of type functions.  TyFun and TsFun below represent an
-- union of one or more of these primitive type functions.
--
-- Since type functions can be arbitrary functions from types to types,
-- there is no algorithmic way to simplify their intersections or unions.
-- Therefore, we represent them as a union of primitive type functions
-- (either arrow types or named closures).
--
-- In particular, we can perform the simplification when unioning (a -> b)
-- and (c -> d) if 'a' and 'c' have a representable intersection.  We could have
-- chosen to make all intersections representable by storing intersections of
-- function types as well, but for now we still stick to storing unions.
data TypeFun t = TypeFun
  { funArrows :: ![(t,t)]
  , funClosures :: ![(Var,[t])] }
  deriving (Eq, Ord, Show)

-- |A concrete type (the types of values are always concrete)
data Type
  = TyCons !CVar [Type]
  | TyFun !(TypeFun Type)
  | TyVoid
  deriving (Eq, Ord, Show)

-- |A set of concrete types (used for function overloads).  This is the same
-- as 'Type' except that it can contain type variables.
data TypeSet
  = TsVar !Var
  | TsCons !CVar [TypeSet]
  | TsFun !(TypeFun TypeSet)
  | TsVoid
  deriving (Eq, Ord, Show)

type TypeEnv = Map Var Type

-- |TypeInfo stores type information about programs for use by the various
-- type manipulation functions.
--
-- typeApply says how to apply closure types to types, and typeVariances
-- gives variance information for datatype constructor.
--
-- Note: skolemization turns type variables into nullary type constructors.
-- To make this work transparently, typeVariances should return [] for
-- nonexistent type constructors.
data TypeInfo m = TypeInfo
  { typeApply :: Type -> Type -> m Type
  , typeVariances :: Var -> [Variance] }

-- |Variance of type constructor arguments.
--
-- Each type argument to a type constructor is treated as either covariant or
-- invariant.  A covariant argument occurs as concrete data, while an invariant
-- type appears as an argument to a function (or similar).  For example, in
--
--     data T a b = A a b (a -> Int)
--
-- "b" is covariant but "a" is invariant.  In terms of subtype relations, we get
--
--     T Int Void <= T Int Int   --   since Void <= Int
--
-- but not
--
--     T Void Int <= T Int Void  -- fails, since the first argument is invariant
--
-- For more explanation of covariance and invariance, see
--     http://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)
data Variance = Covariant | Invariant

-- |Constraints represent constraints on type variables in a typeset
-- or list of typesets.  An entry x -> op t means the final type of x must
-- satisfy S(x) op S(t).
data ConstraintOp = Equal | Superset deriving (Eq)
type Constraints = Map Var (ConstraintOp, Type)

freeze :: Constraints -> TypeEnv
freeze = Map.map snd

-- |Exact type equality
equal :: MonadMaybe m => TypeInfo m -> Type -> Type -> m ()
equal info (TyCons c tl) (TyCons c' tl') | c == c' = mapM_ (uncurry $ equal info) =<< zipCheck tl tl'
equal info (TyFun f) (TyFun f') = equalFun info f f'
equal _ TyVoid TyVoid = success
equal _ _ _ = nothing

-- |Exact type equality for function types.
equalFun :: MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun Type -> m ()
equalFun info f f' = do
  subsetFun'' info f f'
  subsetFun'' info f' f

-- |@z <- union x y@ means that a value of type x or y can be safely viewed as
-- having type z.  Viewed as sets, this means S(z) >= union S(x) S(y), where
-- equality holds if the union of values can be exactly represented as a type.
union :: MonadMaybe m => TypeInfo m -> Type -> Type -> m Type
union info (TyCons c tl) (TyCons c' tl') | c == c' = do
  let var = typeVariances info c
  guard' $ length tl == length tl' && length tl <= length var
  TyCons c =.< zipWith3M arg var tl tl'
  where
  arg Covariant t t' = union info t t'
  arg Invariant t t' = equal info t t' >. t
union info (TyFun f) (TyFun f') = TyFun =.< unionFun info f f'
union _ TyVoid t = return t
union _ t TyVoid = return t
union _ _ _ = nothing

-- |The equivalent of 'union' for lists.  The two lists must have the same size.
_unionList :: MonadMaybe m => TypeInfo m -> [Type] -> [Type] -> m [Type]
_unionList info tl tl' = zipCheck tl tl' >>= mapM (uncurry $ union info)

-- |Union two type functions.  Except in special cases, this means unioning the lists.
unionFun :: MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun Type -> m (TypeFun Type)
unionFun info (TypeFun al cl) (TypeFun al' cl') = do
  al'' <- reduceArrows info (al++al')
  return $ TypeFun (List.sort al'') (merge cl cl')

-- |Given a union list of arrow types, attempt to reduce them into a
-- smaller equivalent list.  This can either successfully reduce, do nothing,
-- or fail (detect that the union is impossible).
reduceArrows :: MonadMaybe m => TypeInfo m -> [(Type,Type)] -> m [(Type,Type)]
reduceArrows _ [] = return []
reduceArrows info ((s,t):al) = do
  r <- reduce [] al
  case r of
    Nothing -> ((s,t) :) =.< reduceArrows info al
    Just al -> reduceArrows info al -- keep trying, maybe we can reduce more
  where
  reduce _ [] = return Nothing
  reduce prev (a@(s',t') : next) = do
    ss <- intersect info s s' -- function arguments are contravariant, so intersect
    case ss of
      Nothing -> reduce (a:prev) next
      Just ss -> do
        tt <- union info t t' -- return values are covariant, so union 
        return $ Just $ (ss,tt) : reverse prev ++ next

-- |@z <- intersect x y@ means that a value of type z can be safely viewed as
-- having type x and type y.  Viewed as sets, S(z) <= intersect S(x) S(y).
--
-- Not all intersections are representable in the case of function types, so
-- intersect can either succeed (the result is representable), fail
-- (intersection is definitely invalid), or be indeterminant (we don't know).
-- The indeterminate case returns Nothing.
intersect :: MonadMaybe m => TypeInfo m -> Type -> Type -> m (Maybe Type)
intersect info (TyCons c tl) (TyCons c' tl') | c == c' = do
  guard' $ length tl == length tl' && length tl <= length var
  fmap (TyCons c) =.< sequence =.< zipWith3M arg var tl tl'
  where
  var = typeVariances info c
  arg Covariant t t' = intersect info t t'
  arg Invariant t t' = equal info t t' >. Just t
intersect _ (TyFun f) (TyFun f') = return (
  if f == f' then Just (TyFun f)
  else Nothing) -- intersect is indeterminant
intersect _ TyVoid _ = return (Just TyVoid)
intersect _ _ TyVoid = return (Just TyVoid)
intersect _ _ _ = nothing

-- |The equivalent of 'intersect' for lists.  The two lists must have the same size.
--
-- If we come across an indeterminate value early in the list, we still process the rest
-- of this in case we find a clear failure.
_intersectList :: MonadMaybe m => TypeInfo m -> [Type] -> [Type] -> m (Maybe [Type])
_intersectList info tl tl' = zipCheck tl tl' >>= mapM (uncurry $ intersect info) >.= sequence

-- |@subset s t@ tries to turn @t@ into @s@ via variable substitutions,
-- but not the other way round.  In other words, subset succeeds if it finds
-- a variable substituion M s.t. S(s) <= S(t|M).
--
-- Note that the occurs check is unnecessary here due to directedness.  In
-- particular, all constraint bindings are of the form v -> t, where t is a Type.
-- Since Type contains no type variables, the occurs check succeeds trivially.
--
-- Operationally, @subset x y@ answers the question "Can we pass an x to a
-- function that takes y?"  As an example, @subset Void x@ always succeeds
-- since the hypothesis is vacuously true: there are no values of type Void.
--
-- The order in which subtypes are unified must be adaptive in the presence of
-- function type sets.  For example, in subset (Negate, Int) (a -> Int, a),
-- the value of "a" must be determined from the second part of the tuple before
-- the function part can be checked.  To handle this, subset' produces a list
-- of indeterminate subcomputations as it runs, and subset iterates on this
-- until a fixed point is reached.
subset :: MonadMaybe m => TypeInfo m -> Type -> TypeSet -> m (TypeEnv, Leftovers)
subset info t t' = subset' info t t' Map.empty >>= subsetFix info Map.empty >.= first freeze

type Leftover = (Type, TypeSet)
type Leftovers = [Leftover]

type Env m = Constraints -> m (Constraints, Leftovers)

successS :: Monad m => Env m
successS env = return (env,[])

failureS :: MonadMaybe m => Env m
failureS _ = nothing

sequenceS :: Monad m => [Env m] -> Env m
sequenceS [] env = return (env,[])
sequenceS (x:xl) env = do
  (env,l1) <- x env
  (env,l2) <- sequenceS xl env
  return (env,l1++l2)

subsetFix :: MonadMaybe m => TypeInfo m -> Constraints -> (Constraints, Leftovers) -> m (Constraints, Leftovers)
subsetFix _ _ r@(_, []) = return r -- finished leftovers, so done
subsetFix _ prev r@(env, _) | prev == env = return r -- reached fixpoint without exhausing leftovers
subsetFix info _ (env, leftovers) = subsetFix info env =<< foldM step (env, []) leftovers where
  step (env, leftovers) (t,t') = do
    (env, l) <- subset' info t t' env
    return (env, l ++ leftovers)

-- For each var in the list, change any Superset constraints to Equal.
freezeVars :: Constraints -> [Var] -> Constraints
freezeVars = foldl (\env v -> Map.adjust (first (const Equal)) v env)

constrain :: MonadMaybe m => TypeInfo m -> Var -> ConstraintOp -> Type -> Env m
constrain info v op t env = c op (Map.lookup v env) where
  c op Nothing = return (Map.insert v (op,t) env,[])
  c Superset (Just (Superset,t')) = union info t t' >.= \t'' -> (Map.insert v (Superset,t'') env,[])
  c Equal    (Just (Superset,t')) = subset'' info t' t >. (Map.insert v (Equal,t) env,[])
  c Superset (Just (Equal,t')) = subset'' info t t' >. (env,[])
  c Equal    (Just (Equal,t')) = equal info t t' >. (env,[])

subset' :: MonadMaybe m => TypeInfo m -> Type -> TypeSet -> Env m
subset' info t (TsVar v) = constrain info v Superset t
subset' info (TyCons c tl) (TsCons c' tl') | c == c' = \env -> do
  guard' $ length tl == length tl' && length tl <= length var
  sequenceS (zipWith3 arg var tl tl') env
  where
  var = typeVariances info c
  arg Covariant t t' = subset' info t t'
  arg Invariant t t' = equal' info t t'
subset' info (TyFun f) (TsFun f') = subsetFun' info f f'
subset' _ TyVoid _ = successS
subset' _ _ _ = failureS

equal' :: MonadMaybe m => TypeInfo m -> Type -> TypeSet -> Env m
equal' info t (TsVar v) = constrain info v Equal t
equal' info (TyCons c tl) (TsCons c' tl') | c == c' = \env -> do
  guard' $ length tl == length tl' && length tl <= length var
  sequenceS (zipWith (equal' info) tl tl') env
  where var = typeVariances info c
equal' info (TyFun f) (TsFun f') = equalFun' info f f'
equal' _ TyVoid TsVoid = successS
equal' _ _ _ = failureS

-- |Same as 'subset'', but the first argument is a type.
-- subset s t succeeds if S(s) <= S(t).
subset'' :: MonadMaybe m => TypeInfo m -> Type -> Type -> m ()
subset'' info (TyCons c tl) (TyCons c' tl') | c == c' = subsetList'' info tl tl'
subset'' info (TyFun f) (TyFun f') = subsetFun'' info f f'
subset'' _ TyVoid _ = success
subset'' _ _ _ = nothing

-- |Subset for function types
--
-- We use the following rules:
--     subset (union_f f) (union_f' f')
--        = forall_f exists_f' (subset f f')
--     subset (a -> b) (c -> d) = subset c a & subset b d
--     subset closure (a -> b) = subset (closure a) b
--     subset (a -> b) closure = false
-- TODO: Currently all we know is that m is a MonadMaybe, and therefore we
-- lack the ability to do speculative computation and rollback.  Therefore,
-- "intersect" currently means ignore all but the first entry.
subsetFun' :: forall m. MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun TypeSet -> Env m
subsetFun' info ft@(TypeFun al cl) ft'@(TypeFun al' cl') = sequenceS (map (arrow al' cl') al ++ map (closure al' cl') cl) where
  arrow :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Type,Type) -> Constraints -> m (Constraints, Leftovers)
  arrow al' _ f env
    | List.elem (singleton f) al' = return (env,[]) -- succeed if f appears in al'
  arrow ((s',t'):_) _ f env = do
    case unsingleton' env s' of
      Nothing -> return (env,[(TyFun ft,TsFun ft')])
      Just s'' -> do
        t <- typeApply info (TyFun (TypeFun [f] [])) s''
        let env' = freezeVars env (freeVars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' info t t' env'
  arrow [] _ _ _ = nothing

  closure :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Var,[Type]) -> Constraints -> m (Constraints, Leftovers)
  closure _ fl' f env
    | List.elem (singleton f) fl' = return (env,[]) -- succeed if f appears in fl'
  closure ((s',t'):_) _ f env = do
    case unsingleton' env s' of
      Nothing -> return (env,[(TyFun ft,TsFun ft')])
      Just s'' -> do
        t <- typeApply info (TyFun (TypeFun [] [f])) s''
        let env' = freezeVars env (freeVars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' info t t' env'
  closure [] _ _ _ = nothing

-- TODO: This is implemented only for primitive functions (single entry TypeFun's)
equalFun' :: forall m. MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun TypeSet -> Env m
equalFun' info (TypeFun [(s,t)] []) (TypeFun [(s',t')] []) = sequenceS [equal' info s s', equal' info t t']
equalFun' info (TypeFun [] [(v,tl)]) (TypeFun [] [(v',tl')]) | v == v', length tl == length tl' = sequenceS (zipWith (equal' info) tl tl')
equalFun' _ _ _ = failureS

-- |Subset for singleton function types.
subsetFun'' :: forall m. MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun Type -> m ()
subsetFun'' info (TypeFun al cl) (TypeFun al' cl') = do
  mapM_ (arrow al' cl') al
  mapM_ (closure al' cl') cl
  where
  arrow :: [(Type,Type)] -> [(Var,[Type])] -> (Type,Type) -> m ()
  arrow al' _ a | List.elem a al' = success -- succeed if a appears in al'
  arrow ((s',t'):_) _ (s,t) = do
    subset'' info s' s -- contravariant
    subset'' info t t' -- covariant
  arrow [] _ _ = nothing -- arrows are never considered as general as closures

  closure :: [(Type,Type)] -> [(Var,[Type])] -> (Var,[Type]) -> m ()
  closure _ fl' f | List.elem f fl' = success -- succeed if f appears in fl'
  closure ((s',t'):_) _ f = do
    t <- typeApply info (TyFun (TypeFun [] [f])) s'
    subset'' info t t'
  closure [] _ _ = nothing

-- |The equivalent of 'subset' for lists.  To succeed, the second argument must
-- be at least as long as the first (think of the first as being the types of
-- values passed to a function taking the second as arguments).
subsetList :: MonadMaybe m => TypeInfo m -> [Type] -> [TypeSet] -> m (TypeEnv, Leftovers)
subsetList info tl tl' = subsetList' info tl tl' Map.empty >>= subsetFix info Map.empty >.= first freeze

subsetList' :: MonadMaybe m => TypeInfo m -> [Type] -> [TypeSet] -> Env m
subsetList' info tl tl'
  | length tl <= length tl' = sequenceS $ zipWith (subset' info) tl tl'
  | otherwise = failureS

-- |Same as 'subsetList'', but for Type instead of TypeSet
subsetList'' :: MonadMaybe m => TypeInfo m -> [Type] -> [Type] -> m ()
subsetList'' info tl tl'
  | length tl <= length tl' = zipWithM_ (subset'' info) tl tl'
  | otherwise = nothing

-- |Check whether one typeset list is a specialization of another.  Note that
-- "specialization" is very different from "subset" in that it ignores the
-- variances of type arguments and some details of function types.
--
-- Since this function is used only for overload decisions, the soundness of
-- type system does not depend on its correctness.  This is why it is safe to
-- ignore the covariant/invariant distinction.
_specialization :: TypeSet -> TypeSet -> Bool
_specialization t t' = isJust (specialization' t t' Map.empty)

specialization' :: TypeSet -> TypeSet -> Map Var TypeSet -> Maybe (Map Var TypeSet)
specialization' t (TsVar v') env =
  case Map.lookup v' env of
    Nothing -> Just (Map.insert v' t env)
    Just t2 | t == t2 -> Just env
    Just _ -> Nothing
specialization' (TsCons c tl) (TsCons c' tl') env | c == c' = specializationList' tl tl' env
specialization' (TsFun f) (TsFun f') env = specializationFun' f f' env
specialization' _ _ _ = Nothing

specializationList :: [TypeSet] -> [TypeSet] -> Bool
specializationList tl tl' = isJust (specializationList' tl tl' Map.empty)

specializationList' :: [TypeSet] -> [TypeSet] -> Map Var TypeSet -> Maybe (Map Var TypeSet)
specializationList' tl tl' env = foldl (>>=) (return env) =<< zipWithCheck specialization' tl tl'

specializationFun' :: TypeFun TypeSet -> TypeFun TypeSet -> Map Var TypeSet -> Maybe (Map Var TypeSet)
specializationFun' (TypeFun al cl) (TypeFun al' cl') env = foldl (>>=) (return env) (map arrow al' ++ map closure cl') where
  -- Succeed if we can find some left-hand function that specializes us
  arrow :: (TypeSet,TypeSet) -> Map Var TypeSet -> Maybe (Map Var TypeSet)
  arrow (_,t') env | List.null cl = msum $ map (\ (_,t) -> specialization' t t' env) al
                   | otherwise = Just env -- treat closures as specializations of all arrow
  closure c' env = if List.elem c' cl then Just env else Nothing

-- |Type environment substitution
subst :: TypeEnv -> TypeSet -> TypeSet
subst env (TsVar v)
  | Just t <- Map.lookup v env = singleton t
  | otherwise = TsVar v
subst env (TsCons c tl) = TsCons c (map (subst env) tl)
subst env (TsFun f) = TsFun (substFun env f)
subst _ TsVoid = TsVoid

substFun :: TypeEnv -> TypeFun TypeSet -> TypeFun TypeSet
substFun env (TypeFun al cl) = TypeFun (map arrow al) (map closure cl) where
  arrow (s,t) = (subst env s, subst env t)
  closure (f,tl) = (f, map (subst env) tl)

-- |Type environment substitution with unbound type variables defaulting to void
substVoid :: TypeEnv -> TypeSet -> Type
substVoid env (TsVar v) = Map.findWithDefault TyVoid v env
substVoid env (TsCons c tl) = TyCons c (map (substVoid env) tl)
substVoid env (TsFun f) = TyFun (substVoidFun env f)
substVoid _ TsVoid = TyVoid

substVoidFun :: TypeEnv -> TypeFun TypeSet -> TypeFun Type
substVoidFun env (TypeFun al cl) = TypeFun (map arrow al) (map closure cl) where
  arrow (s,t) = (substVoid env s, substVoid env t)
  closure (f,tl) = (f, map (substVoid env) tl)

-- |Occurs check
occurs :: TypeEnv -> Var -> TypeSet -> Bool
occurs env v (TsVar v') | Just t <- Map.lookup v' env = occurs' v t
occurs _ v (TsVar v') = v == v'
occurs env v (TsCons _ tl) = any (occurs env v) tl
occurs env v (TsFun f) = occursFun env v f
occurs _ _ TsVoid = False

occursFun :: TypeEnv -> Var -> TypeFun TypeSet -> Bool
occursFun env v (TypeFun al cl) = any arrow al || any closure cl where
  arrow (s,t) = occurs env v s || occurs env v t
  closure (_,tl) = any (occurs env v) tl

-- |Types contains no variables
occurs' :: Var -> Type -> Bool
occurs' _ _ = False

-- |This way is easy
--
-- For convenience, we overload the singleton function a lot.
class Singleton a b | a -> b where
  singleton :: a -> b

instance Singleton Type TypeSet where
  singleton (TyCons c tl) = TsCons c (singleton tl)
  singleton (TyFun f) = TsFun (singleton f)
  singleton TyVoid = TsVoid

instance Singleton a b => Singleton [a] [b] where
  singleton = map singleton

instance (Singleton a b, Singleton a' b') => Singleton (a,a') (b,b') where
  singleton (s,t) = (singleton s, singleton t)

instance Singleton Var Var where
  singleton = id

instance Singleton a b => Singleton (TypeFun a) (TypeFun b) where
  singleton (TypeFun al cl) = TypeFun (singleton al) (singleton cl)
 
-- |Convert a singleton typeset to a type if possible
unsingleton :: TypeSet -> Maybe Type
unsingleton = unsingleton' Map.empty

unsingleton' :: Constraints -> TypeSet -> Maybe Type
unsingleton' env (TsVar v) | Just (_,t) <- Map.lookup v env = return t
unsingleton' _ (TsVar _) = nothing
unsingleton' env (TsCons c tl) = TyCons c =.< mapM (unsingleton' env) tl
unsingleton' env (TsFun f) = TyFun =.< unsingletonFun' env f
unsingleton' _ TsVoid = return TyVoid

unsingletonFun' :: Constraints -> TypeFun TypeSet -> Maybe (TypeFun Type)
unsingletonFun' env (TypeFun al cl) = do
  al <- mapM arrow al
  cl <- mapM closure cl
  return $ TypeFun al cl
  where
  arrow (s,t) = do
    s <- unsingleton' env s
    t <- unsingleton' env t
    return (s,t)
  closure (f,tl) = mapM (unsingleton' env) tl >.= \tl -> (f,tl)

-- TODO: I'm being extremely cavalier here and pretending that the space of
-- variables in TsCons and TsVar is disjoint.  When this fails in the future,
-- skolemize will need to be fixed to turn TsVar variables into fresh TyCons
-- variables.
_ignore = skolemize
skolemize :: TypeSet -> Type
skolemize (TsVar v) = TyCons v [] -- skolemization
skolemize (TsCons c tl) = TyCons c (map skolemize tl)
skolemize (TsFun f) = TyFun (skolemizeFun f)
skolemize TsVoid = TyVoid

skolemizeFun :: TypeFun TypeSet -> TypeFun Type
skolemizeFun (TypeFun al cl) = TypeFun (map arrow al) (map closure cl) where
  arrow (s,t) = (skolemize s, skolemize t)
  closure (f,tl) = (f, map skolemize tl)

-- |Find the set of free variables in a typeset
freeVars :: TypeSet -> [Var]
freeVars (TsVar v) = [v]
freeVars (TsCons _ tl) = concatMap freeVars tl
freeVars (TsFun (TypeFun al cl)) = concatMap arrow al ++ concatMap closure cl where
  arrow (s,t) = freeVars s ++ freeVars t
  closure (_,tl) = concatMap freeVars tl
freeVars TsVoid = []

-- |If leftovers remain after unification, this function explains which
-- variables caused the problem.
contravariantVars :: Leftovers -> [Var]
contravariantVars = concatMap (cv . snd) where
  cv (TsVar _) = []
  cv (TsCons _ tl) = concatMap cv tl
  cv (TsFun (TypeFun al _)) = concatMap (freeVars . fst) al
  cv TsVoid = []

showContravariantVars :: Leftovers -> String
showContravariantVars leftovers = case contravariantVars leftovers of
  [v] -> "variable "++pshow v
  vl -> "variables "++List.intercalate ", " (map pshow vl)
 
-- Pretty printing

instance Pretty TypeSet where
  pretty' (TsVar v) = pretty' v
  pretty' (TsCons t []) = pretty' t
  pretty' (TsCons t tl) | istuple t = (2, hcat $ List.intersperse (pretty ", ") $ map (guard 3) tl)
  pretty' (TsCons t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
  pretty' (TsFun f) = pretty' f
  pretty' TsVoid = (100, pretty "Void")

instance Pretty Type where
  pretty' = pretty' . singleton

instance Pretty t => Pretty (TypeFun t) where
  pretty' (TypeFun [] [(f,[])]) = pretty' f
  pretty' (TypeFun [(s,t)] []) = (1, guard 2 s <+> pretty "->" <+> guard 1 t)
  pretty' (TypeFun [] [(f,tl)]) = (50, pretty f <+> prettylist tl)
  pretty' (TypeFun al cl) = (40, hsep (List.intersperse (pretty "&") (
    map (\ (s,t) -> parens (guard 2 s <+> pretty "->" <+> guard 1 t)) al ++
    map (\ (f,tl) -> pretty f <+> prettylist tl) cl)))
