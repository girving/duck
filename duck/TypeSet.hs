{-# LANGUAGE ScopedTypeVariables, PatternGuards, FlexibleContexts #-}
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
  ( TypeMonad(..)
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
import Control.Monad.State
import Control.Monad.Error.Class

import Util
import SrcLoc
import Pretty
import Var
import Type
import InferMonad

-- |TypeMonad stores type information about programs for use by the various
-- type manipulation functions.
--
-- 'typeApply' says how to apply closure types to types, and 'typeVariances'
-- gives variance information for datatype constructor.
--
-- Note: skolemization turns type variables into nullary type constructors.
-- To make this work transparently, 'typeVariances' should return [] for
-- nonexistent type constructors.
class MonadError TypeError m => TypeMonad m where
  typeApply :: Type -> Type -> m Type
  typeVariances :: Var -> m [Variance]

-- |Constraints represent constraints on type variables in a typeset
-- or list of typesets.  An entry x -> op t means the final type of x must
-- satisfy S(x) op S(t).
data ConstraintOp = Equal | Superset deriving (Eq)
type Constraints = Map Var (ConstraintOp, Type)

typeMismatchList x y = typeMismatch (prettylist x) (prettylist y)

freeze :: Constraints -> TypeEnv
freeze = Map.map snd

-- |Exact type equality
equal :: TypeMonad m => Type -> Type -> m ()
equal (TyCons c tl) (TyCons c' tl')
  | c == c'
  , Just tt <- zipCheck tl tl'
  = mapM_ (uncurry equal) tt
equal (TyFun f) (TyFun f') = equalFun f f'
equal TyVoid TyVoid = success
equal x y = typeMismatch x y

-- |Exact type equality for function types.
equalFun :: TypeMonad m => TypeFun Type -> TypeFun Type -> m ()
equalFun f f' = do
  subsetFun'' f f'
  subsetFun'' f' f

zipWithVariances :: (TypeMonad m, Pretty a, Pretty b) => (Variance -> a -> b -> m c) -> CVar -> [a] -> [b] -> m [c]
zipWithVariances f c tl tl' = do
  var <- typeVariances c
  zcv var tl tl' where
    zcv _ [] [] = return []
    zcv (v:vl) (t:tl) (t':tl') = f v t t' >>= \z -> zcv vl tl tl' >.= (z:)
    zcv [] _ _ = typeError noLoc (qshow c ++ " applied to too many arguments")
    zcv _ tl tl' = typeError noLoc (qshow c ++ " missing arguments " ++ qshow (map pretty tl ++ map pretty tl'))

-- |@z <- union x y@ means that a value of type x or y can be safely viewed as
-- having type z.  Viewed as sets, this means S(z) >= union S(x) S(y), where
-- equality holds if the union of values can be exactly represented as a type.
union :: TypeMonad m => Type -> Type -> m Type
union (TyCons c tl) (TyCons c' tl') | c == c' =
  TyCons c =.< zipWithVariances arg c tl tl' where
  arg Covariant t t' = union t t'
  arg Invariant t t' = equal t t' >. t
union (TyFun f) (TyFun f') = TyFun =.< unionFun f f'
union TyVoid t = return t
union t TyVoid = return t
union x y = typeMismatch x y

-- |The equivalent of 'union' for lists.  The two lists must have the same size.
_unionList :: TypeMonad m => [Type] -> [Type] -> m [Type]
_unionList tl tl'
  | Just tt <- zipCheck tl tl' = mapM (uncurry union) tt
  | otherwise = typeMismatchList tl tl'

-- |Union two type functions.  Except in special cases, this means unioning the lists.
unionFun :: TypeMonad m => TypeFun Type -> TypeFun Type -> m (TypeFun Type)
unionFun (TypeFun al cl) (TypeFun al' cl') = do
  al'' <- reduceArrows (al++al')
  return $ TypeFun (List.sort al'') (merge cl cl')

-- |Given a union list of arrow types, attempt to reduce them into a
-- smaller equivalent list.  This can either successfully reduce, do nothing,
-- or fail (detect that the union is impossible).
reduceArrows :: TypeMonad m => [(Type,Type)] -> m [(Type,Type)]
reduceArrows [] = return []
reduceArrows ((s,t):al) = do
  r <- reduce [] al
  case r of
    Nothing -> ((s,t) :) =.< reduceArrows al
    Just al -> reduceArrows al -- keep trying, maybe we can reduce more
  where
  reduce _ [] = return Nothing
  reduce prev (a@(s',t') : next) = do
    ss <- intersect s s' -- function arguments are contravariant, so intersect
    case ss of
      Nothing -> reduce (a:prev) next
      Just ss -> do
        tt <- union t t' -- return values are covariant, so union 
        return $ Just $ (ss,tt) : reverse prev ++ next

-- |@z <- intersect x y@ means that a value of type z can be safely viewed as
-- having type x and type y.  Viewed as sets, S(z) <= intersect S(x) S(y).
--
-- Not all intersections are representable in the case of function types, so
-- intersect can either succeed (the result is representable), fail
-- (intersection is definitely invalid), or be indeterminant (we don't know).
-- The indeterminate case returns Nothing.
intersect :: TypeMonad m => Type -> Type -> m (Maybe Type)
intersect (TyCons c tl) (TyCons c' tl') | c == c' =
  fmap (TyCons c) =.< sequence =.< zipWithVariances arg c tl tl' where
  arg Covariant t t' = intersect t t'
  arg Invariant t t' = equal t t' >. Just t
intersect (TyFun f) (TyFun f') = return (
  if f == f' then Just (TyFun f)
  else Nothing) -- intersect is indeterminant
intersect TyVoid _ = return (Just TyVoid)
intersect _ TyVoid = return (Just TyVoid)
intersect x y = typeMismatch x y

-- |The equivalent of 'intersect' for lists.  The two lists must have the same size.
--
-- If we come across an indeterminate value early in the list, we still process the rest
-- of this in case we find a clear failure.
_intersectList :: TypeMonad m => [Type] -> [Type] -> m (Maybe [Type])
_intersectList tl tl'
  | Just tt <- zipCheck tl tl' = mapM (uncurry intersect) tt >.= sequence
  | otherwise = typeMismatchList tl tl'

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
subset :: TypeMonad m => Type -> TypePat -> m (TypeEnv, Leftovers)
subset t t' = runEnv $ subset' t t' >>= subsetFix Map.empty

type Leftover = (Type, TypePat)
type Leftovers = [Leftover]

type EnvM m a = StateT Constraints m a
type Env m = EnvM m Leftovers

instance TypeMonad m => TypeMonad (StateT s m) where
  typeApply t = lift . typeApply t
  typeVariances = lift . typeVariances

runEnv :: Monad m => Env m -> m (TypeEnv, Leftovers)
runEnv m = runStateT m Map.empty >.= flp . second freeze

successS :: Monad m => Env m
successS = return []

lookupS :: Monad m => Var -> EnvM m (Maybe (ConstraintOp, Type))
lookupS v = get >.= Map.lookup v

insertS :: Monad m => Var -> (ConstraintOp, Type) -> Env m
insertS v c = modify (Map.insert v c) >> successS

freezeS :: Monad m => EnvM m TypeEnv
freezeS = get >.= freeze

sequenceS :: Monad m => [Env m] -> Env m
sequenceS l = concat =.< sequence l

subsetFix :: TypeMonad m => Constraints -> Leftovers -> Env m
subsetFix _ [] = successS -- finished leftovers, so done
subsetFix prev leftovers = do
  env <- get
  if prev == env
    then return leftovers -- reached fixpoint without exhausing leftovers
    else subsetFix env =<< foldM step [] leftovers where
  step leftovers (t,t') = (++ leftovers) =.< subset' t t'

-- For each var in the list, change any Superset constraints to Equal.
freezeVars :: [Var] -> Constraints -> Constraints
freezeVars vl c = foldr (Map.adjust (first (const Equal))) c vl

constrain :: TypeMonad m => Var -> ConstraintOp -> Type -> Env m
constrain v op t = c op =<< lookupS v where
  c op Nothing = insertS v (op,t)
  c Superset (Just (Superset,t')) = lift (union t t') >>= \t'' -> insertS v (Superset,t'')
  c Equal    (Just (Superset,t')) = lift (subset'' t' t) >> insertS v (Equal,t)
  c Superset (Just (Equal,t')) = lift (subset'' t t') >> successS
  c Equal    (Just (Equal,t')) = lift (equal t t') >> successS

subset' :: forall m. TypeMonad m => Type -> TypePat -> Env m
subset' t (TsVar v) = constrain v Superset t
subset' (TyCons c tl) (TsCons c' tl') | c == c' =
  sequenceS =<< zipWithVariances (\v t -> return . arg v t) c tl tl' where
  arg :: Variance -> Type -> TypePat -> Env m
  arg Covariant t t' = subset' t t'
  arg Invariant t t' = equal' t t'
subset' (TyFun f) (TsFun f') = subsetFun' f f'
subset' TyVoid _ = successS
subset' x y = typeMismatch x y

equal' :: TypeMonad m => Type -> TypePat -> Env m
equal' t (TsVar v) = constrain v Equal t
equal' (TyCons c tl) (TsCons c' tl') | c == c' =
  sequenceS =<< zipWithVariances (\_ t -> return . equal' t) c tl tl'
equal' (TyFun f) (TsFun f') = equalFun' f f'
equal' TyVoid TsVoid = successS
equal' x y = typeMismatch x y

-- |Same as 'subset'', but the first argument is a type.
-- subset s t succeeds if S(s) <= S(t).
subset'' :: TypeMonad m => Type -> Type -> m ()
subset'' (TyCons c tl) (TyCons c' tl') | c == c' = subsetList'' tl tl'
subset'' (TyFun f) (TyFun f') = subsetFun'' f f'
subset'' TyVoid _ = success
subset'' x y = typeMismatch x y

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
-- TODO: Currently all we know is that m is a 'TypeMonad', and therefore we
-- lack the ability to do speculative computation and rollback.  Therefore,
-- 'intersect' currently means ignore all but the first entry.
subsetFun' :: forall m. TypeMonad m => TypeFun Type -> TypeFun TypePat -> Env m
subsetFun' ft@(TypeFun al cl) ft'@(TypeFun al' cl') = sequenceS (map (arrow al' cl') al ++ map (closure al' cl') cl) where
  arrow :: [(TypePat,TypePat)] -> [(Var,[TypePat])] -> (Type,Type) -> Env m
  arrow al' _ f
    | List.elem (singleton f) al' = successS -- succeed if f appears in al'
  arrow ((s',t'):_) _ f = do
    tenv <- freezeS
    case unsingleton' tenv s' of
      Nothing -> return [(TyFun ft,TsFun ft')]
      Just s'' -> do
        t <- typeApply (TyFun (TypeFun [f] [])) s''
        withStateT (freezeVars (freeVars s')) $ -- We're about to feed these vars to apply, so they'll become rigid
          subset' t t'
  arrow [] _ _ = typeMismatch (TyFun ft) (TsFun ft')

  closure :: [(TypePat,TypePat)] -> [(Var,[TypePat])] -> (Var,[Type]) -> Env m
  closure _ fl' f
    | List.elem (singleton f) fl' = successS -- succeed if f appears in fl'
  closure ((s',t'):_) _ f = do
    tenv <- freezeS
    case unsingleton' tenv s' of
      Nothing -> return [(TyFun ft,TsFun ft')]
      Just s'' -> do
        t <- typeApply (TyFun (TypeFun [] [f])) s''
        withStateT (freezeVars (freeVars s')) $ -- We're about to feed these vars to apply, so they'll become rigid
          subset' t t'
  closure [] _ _ = typeMismatch (TyFun ft) (TsFun ft')

-- TODO: This is implemented only for primitive functions (single entry TypeFun's)
equalFun' :: forall m. TypeMonad m => TypeFun Type -> TypeFun TypePat -> Env m
equalFun' (TypeFun [(s,t)] []) (TypeFun [(s',t')] []) = sequenceS [equal' s s', equal' t t']
equalFun' (TypeFun [] [(v,tl)]) (TypeFun [] [(v',tl')]) | v == v', length tl == length tl' = sequenceS (zipWith equal' tl tl')
equalFun' x y = typeMismatch (TyFun x) (TsFun y)

-- |Subset for singleton function types.
subsetFun'' :: forall m. TypeMonad m => TypeFun Type -> TypeFun Type -> m ()
subsetFun'' ft@(TypeFun al cl) ft'@(TypeFun al' cl') = do
  mapM_ (arrow al' cl') al
  mapM_ (closure al' cl') cl
  where
  arrow :: [(Type,Type)] -> [(Var,[Type])] -> (Type,Type) -> m ()
  arrow al' _ a | List.elem a al' = success -- succeed if a appears in al'
  arrow ((s',t'):_) _ (s,t) = do
    subset'' s' s -- contravariant
    subset'' t t' -- covariant
  arrow [] _ _ = typeMismatch (TyFun ft) (TyFun ft') -- arrows are never considered as general as closures

  closure :: [(Type,Type)] -> [(Var,[Type])] -> (Var,[Type]) -> m ()
  closure _ fl' f | List.elem f fl' = success -- succeed if f appears in fl'
  closure ((s',t'):_) _ f = do
    t <- typeApply (TyFun (TypeFun [] [f])) s'
    subset'' t t'
  closure [] _ _ = typeMismatch (TyFun ft) (TyFun ft')

-- |The equivalent of 'subset' for lists.  To succeed, the second argument must
-- be at least as long as the first (think of the first as being the types of
-- values passed to a function taking the second as arguments).
subsetList :: TypeMonad m => [Type] -> [TypePat] -> m (TypeEnv, Leftovers)
subsetList tl tl' = runEnv $ subsetList' tl tl' >>= subsetFix Map.empty

subsetList' :: TypeMonad m => [Type] -> [TypePat] -> Env m
subsetList' tl tl'
  | length tl <= length tl' = sequenceS $ zipWith subset' tl tl'
  | otherwise = typeMismatchList tl tl'

-- |Same as 'subsetList'', but for 'Type' instead of 'TypePat'
subsetList'' :: TypeMonad m => [Type] -> [Type] -> m ()
subsetList'' tl tl'
  | length tl <= length tl' = zipWithM_ subset'' tl tl'
  | otherwise = typeMismatchList tl tl'

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
 
