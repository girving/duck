{-# LANGUAGE ScopedTypeVariables, PatternGuards #-}
-- | Type "set" operations
--
-- Explanation of covariance and contravariance:
--
-- You should think of a type as being the set of values that inhabit the type.
-- For example, the type Int is {0, 1, -1, 2, -2, ...}, and the type Void is
-- the empty set {}.  Subtype means subset, so Void is a subtype of all types.
-- In some of comments below, we'll use S(t) to denote this set of values.
--
-- The set logic is also useful for remembering what union and intersect do.
-- For example, (if c then a else b :: union A B) if (a :: A) and (b :: B),
-- since the set of values resulting from the \"if\" is the union of the sets of
-- values resulting from the two branches.  Intersection arises as the
-- contravariant version of union:
--
-- >   union (a -> t) (b -> t) = intersect a b -> t
--
-- Note that Void is equivalent to the Haskell type forall a. a.  On the other
-- side of the lattice, the type Top corresponding to the type exists a. a would
-- be the type that could be anything.
--
-- A concrete example: the empty list [] has type List Void.  If we start adding
-- values to the list to get [a], [a,b], etc. the type gets larger and larger
-- as we union together more and more types.

module TypeSet
  ( TypeInfo(..)
  , subset
  , subset''
  , subsetList
  , subsetList''
  , specializationList
  , union
  , contravariantVars
  , showContravariantVars
  ) where

import Data.Maybe
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad hiding (guard)

import Util
import Pretty
import Var
import Type

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
-- Operationally, @subset x y@ answers the question \"Can we pass an x to a
-- function that takes y?\"  As an example, @subset Void x@ always succeeds
-- since the hypothesis is vacuously true: there are no values of type Void.
--
-- The order in which subtypes are unified must be adaptive in the presence of
-- function type sets.  For example, in subset (Negate, Int) (a -> Int, a),
-- the value of \"a\" must be determined from the second part of the tuple before
-- the function part can be checked.  To handle this, subset' produces a list
-- of indeterminate subcomputations as it runs, and subset iterates on this
-- until a fixed point is reached.
subset :: MonadMaybe m => TypeInfo m -> Type -> TypePat -> m (TypeEnv, Leftovers)
subset info t t' = subset' info t t' Map.empty >>= subsetFix info Map.empty >.= first freeze

type Leftover = (Type, TypePat)
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

subset' :: MonadMaybe m => TypeInfo m -> Type -> TypePat -> Env m
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

equal' :: MonadMaybe m => TypeInfo m -> Type -> TypePat -> Env m
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
--
-- @
--     subset (union_f f) (union_f' f')
--        = forall_f exists_f' (subset f f')
--     subset (a -> b) (c -> d) = subset c a & subset b d
--     subset closure (a -> b) = subset (closure a) b
--     subset (a -> b) closure = false
-- @
--
-- TODO: Currently all we know is that m is a 'MonadMaybe', and therefore we
-- lack the ability to do speculative computation and rollback.  Therefore,
-- 'intersect' currently means ignore all but the first entry.
subsetFun' :: forall m. MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun TypePat -> Env m
subsetFun' info ft@(TypeFun al cl) ft'@(TypeFun al' cl') = sequenceS (map (arrow al' cl') al ++ map (closure al' cl') cl) where
  arrow :: [(TypePat,TypePat)] -> [(Var,[TypePat])] -> (Type,Type) -> Constraints -> m (Constraints, Leftovers)
  arrow al' _ f env
    | List.elem (singleton f) al' = return (env,[]) -- succeed if f appears in al'
  arrow ((s',t'):_) _ f env = do
    case unsingleton' (freeze env) s' of
      Nothing -> return (env,[(TyFun ft,TsFun ft')])
      Just s'' -> do
        t <- typeApply info (TyFun (TypeFun [f] [])) s''
        let env' = freezeVars env (freeVars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' info t t' env'
  arrow [] _ _ _ = nothing

  closure :: [(TypePat,TypePat)] -> [(Var,[TypePat])] -> (Var,[Type]) -> Constraints -> m (Constraints, Leftovers)
  closure _ fl' f env
    | List.elem (singleton f) fl' = return (env,[]) -- succeed if f appears in fl'
  closure ((s',t'):_) _ f env = do
    case unsingleton' (freeze env) s' of
      Nothing -> return (env,[(TyFun ft,TsFun ft')])
      Just s'' -> do
        t <- typeApply info (TyFun (TypeFun [] [f])) s''
        let env' = freezeVars env (freeVars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' info t t' env'
  closure [] _ _ _ = nothing

-- TODO: This is implemented only for primitive functions (single entry TypeFun's)
equalFun' :: forall m. MonadMaybe m => TypeInfo m -> TypeFun Type -> TypeFun TypePat -> Env m
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
subsetList :: MonadMaybe m => TypeInfo m -> [Type] -> [TypePat] -> m (TypeEnv, Leftovers)
subsetList info tl tl' = subsetList' info tl tl' Map.empty >>= subsetFix info Map.empty >.= first freeze

subsetList' :: MonadMaybe m => TypeInfo m -> [Type] -> [TypePat] -> Env m
subsetList' info tl tl'
  | length tl <= length tl' = sequenceS $ zipWith (subset' info) tl tl'
  | otherwise = failureS

-- |Same as 'subsetList'', but for 'Type' instead of 'TypePat'
subsetList'' :: MonadMaybe m => TypeInfo m -> [Type] -> [Type] -> m ()
subsetList'' info tl tl'
  | length tl <= length tl' = zipWithM_ (subset'' info) tl tl'
  | otherwise = nothing

-- |Check whether one typeset list is a specialization of another.  Note that
-- 'specialization' is very different from 'subset' in that it ignores the
-- variances of type arguments and some details of function types.
--
-- Since this function is used only for overload decisions, the soundness of
-- type system does not depend on its correctness.  This is why it is safe to
-- ignore the covariant/invariant distinction.
_specialization :: TypePat -> TypePat -> Bool
_specialization t t' = isJust (specialization' t t' Map.empty)

specialization' :: TypePat -> TypePat -> Map Var TypePat -> Maybe (Map Var TypePat)
specialization' t (TsVar v') env =
  case Map.lookup v' env of
    Nothing -> Just (Map.insert v' t env)
    Just t2 | t == t2 -> Just env
    Just _ -> Nothing
specialization' (TsCons c tl) (TsCons c' tl') env | c == c' = specializationList' tl tl' env
specialization' (TsFun f) (TsFun f') env = specializationFun' f f' env
specialization' _ _ _ = Nothing

specializationList :: [TypePat] -> [TypePat] -> Bool
specializationList tl tl' = isJust (specializationList' tl tl' Map.empty)

specializationList' :: [TypePat] -> [TypePat] -> Map Var TypePat -> Maybe (Map Var TypePat)
specializationList' tl tl' env = foldl (>>=) (return env) =<< zipWithCheck specialization' tl tl'

specializationFun' :: TypeFun TypePat -> TypeFun TypePat -> Map Var TypePat -> Maybe (Map Var TypePat)
specializationFun' (TypeFun al cl) (TypeFun al' cl') env = foldl (>>=) (return env) (map arrow al' ++ map closure cl') where
  -- Succeed if we can find some left-hand function that specializes us
  arrow :: (TypePat,TypePat) -> Map Var TypePat -> Maybe (Map Var TypePat)
  arrow (_,t') env | List.null cl = msum $ map (\ (_,t) -> specialization' t t' env) al
                   | otherwise = Just env -- treat closures as specializations of all arrow
  closure c' env = if List.elem c' cl then Just env else Nothing

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
 
