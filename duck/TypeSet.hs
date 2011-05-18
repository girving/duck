{-# LANGUAGE ScopedTypeVariables, PatternGuards, FlexibleContexts, FlexibleInstances #-}
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
import Prims

-- |TypeMonad stores type information about programs for use by the various
-- type manipulation functions.
class MonadError TypeError m => TypeMonad m where
  -- |How to apply closure types to types, returning the transform to be applied to the argument, along with the result of the application (i.e., not a TransType)
  typeApply :: TypeVal -> TypeVal -> m (Trans, TypeVal)

class TypeSuccess r where
  typeSuccess :: r
  typeConcat :: [r] -> r

instance TypeSuccess () where
  typeSuccess = ()
  typeConcat _ = ()

success :: (TypeMonad m, TypeSuccess r) => m r
success = return typeSuccess

sequenceS :: (TypeMonad m, TypeSuccess r) => [m r] -> m r
sequenceS l = typeConcat =.< sequence l

-- |Constraints represent constraints on type variables in a typeset
-- or list of typesets.  An entry x -> op t means the final type of x must
-- satisfy S(x) op S(t).
data ConstraintOp = Equal | Superset deriving (Eq)
type Constraints = Map Var (ConstraintOp, TypeVal)

typeMismatchList x op y = typeMismatch (hsep x) op (hsep y)

-- |Unify two type constructors, coercing them to be the same and modifying
-- their arguments if possible.
unifyCons :: (TypeMonad m, IsType t, Pretty t) => Datatype -> [TypeVal] -> Datatype -> [t] -> m (Datatype,[TypeVal],[t])
unifyCons c tl c' tl'
  | c == c' = return (c,tl,tl')
  | otherwise = do
    r <- tryError $ coerceCons c tl c'
    case r of
      Right tl -> return (c',tl,tl')
      Left _ -> do
        r <- tryError $ coerceCons c' tl' c
        case r of
          Right tl' -> return (c,tl,tl')
          Left _ -> typeError noLoc $ "type mismatch:" <+> quoted (typeCons c tl) <+> "and" <+> quoted (typeCons c' tl') <+> "have incompatible constructors"

-- |Attempt to coerce one type constructor into another, modifying the
-- arguments accordingly.  This allows equivalences such as
--
--     Type (x,y) = (Type x, Type y)
-- 
-- Note that coerceCons is asymmetric; the symmetry is recovered by applying
-- in both directions from unifyCons.  WARNING: This may change once we add
-- List support.
--
-- For now, the set of type constructor coersions is hard coded.
coerceCons :: (TypeMonad m, IsType t, Pretty t) => Datatype -> [t] -> Datatype -> m [t]
coerceCons c tl c' | c == c' = return tl
coerceCons d [t] c' | d == datatypeType, isDatatypeTuple c', Just (c,tl) <- unTypeCons t = do
  tl <- coerceCons c tl c'
  return $ map typeType tl
coerceCons c tl c' | c' == datatypeType, isDatatypeTuple c, Just ctl <- mapM unTypeCons tl = do
  tl <- mapM (\ (c,tl) -> coerceCons c tl c' >.= \ ~[t] -> t) ctl
  return [typeCons c tl]
coerceCons c tl c' = typeError noLoc $ "cannot coerce" <+> quoted (typeCons c tl) <+> "to have type constructor" <+> quoted c'

zipWithVariances :: (TypeMonad m, Pretty a, Pretty b) => (Variance -> a -> b -> m c) -> Datatype -> [a] -> [b] -> m [c]
zipWithVariances f c tl tl' = do
  let var = dataVariances c
  zcv var tl tl' where
    zcv _ [] [] = return []
    zcv (v:vl) (t:tl) (t':tl') = f v t t' >>= \z -> zcv vl tl tl' >.= (z:)
    zcv [] _ _ = typeError noLoc $ quoted c <+> "applied to too many arguments"
    zcv _ tl tl' = typeError noLoc $ quoted c <+> "missing arguments:" <+> hsep tl <+> hsep tl'

-- |Exact type equality
equal :: TypeMonad m => TypeVal -> TypeVal -> m ()
equal (TyCons c tl) (TyCons c' tl') = do
  (c,tl,tl') <- unifyCons c tl c' tl'
  _ <- zipWithVariances (const equal) c tl tl'
  success
equal (TyFun f) (TyFun f') = equalFun f f'
equal TyVoid TyVoid = success
equal x y = typeMismatch x "==" y

-- |Exact type equality for function types.
equalFun :: TypeMonad m => [TypeFun TypeVal] -> [TypeFun TypeVal] -> m ()
equalFun f f' = do
  subsetFun'' f f'
  subsetFun'' f' f

-- |@z <- union x y@ means that a value of type x or y can be safely viewed as
-- having type z.  Viewed as sets, this means S(z) >= union S(x) S(y), where
-- equality holds if the union of values can be exactly represented as a type.
union :: TypeMonad m => TypeVal -> TypeVal -> m TypeVal
union (TyCons c tl) (TyCons c' tl') = do
  (c,tl,tl') <- unifyCons c tl c' tl'
  TyCons c =.< zipWithVariances arg c tl tl' where
  arg Covariant t t' = union t t'
  arg Invariant t t' = equal t t' >. t
union (TyFun f) (TyFun f') = TyFun =.< reduceFuns (f ++ f')
union TyVoid t = return t
union t TyVoid = return t
union (TyStatic (TV x _)) y = union x y
union x (TyStatic (TV y _)) = union x y
union x y = typeMismatch x "|" y

-- |The equivalent of 'union' for lists.  The two lists must have the same size.
_unionList :: TypeMonad m => [TypeVal] -> [TypeVal] -> m [TypeVal]
_unionList tl tl'
  | Just tt <- zipCheck tl tl' = mapM (uncurry union) tt
  | otherwise = typeMismatchList tl "|" tl'

-- |Given a union list of primitive function types, attempt to reduce them into
-- a smaller equivalent list.  This can either successfully reduce, do nothing,
-- or fail (detect that the union is impossible).
reduceFuns :: TypeMonad m => [TypeFun TypeVal] -> m [TypeFun TypeVal]
reduceFuns [] = return []
reduceFuns (f:fl) = do
  r <- reduce f [] fl
  case r of
    Nothing -> (f:) =.< reduceFuns fl
    Just fl -> reduceFuns fl -- keep trying, maybe we can reduce more
  where
  reduce _ _ [] = return Nothing
  reduce f@(FunArrow tr s t) prev (f'@(FunArrow tr' s' t') : next) = do
    ss <- intersect s s' -- function arguments are contravariant, so intersect
    case (intersectTrans tr tr', ss) of
      (Just tr, Just ss) -> do
        tt <- union t t' -- return values are covariant, so union 
        return $ Just $ FunArrow tr ss tt : reverse prev ++ next
      _ -> reduce f (f':prev) next
  reduce f prev (f' : next) | f == f' = return $ Just $ f : reverse prev ++ next
  reduce f prev (f' : next) = reduce f (f':prev) next

-- |@z <- intersect x y@ means that a value of type z can be safely viewed as
-- having type x and type y.  Viewed as sets, S(z) <= intersect S(x) S(y).
--
-- Not all intersections are representable in the case of function types, so
-- intersect can either succeed (the result is representable), fail
-- (intersection is definitely invalid), or be indeterminant (we don't know).
-- The indeterminate case returns Nothing.
intersect :: TypeMonad m => TypeVal -> TypeVal -> m (Maybe TypeVal)
intersect (TyCons c tl) (TyCons c' tl') = do
  (c,tl,tl') <- unifyCons c tl c' tl'
  fmap (TyCons c) =.< sequence =.< zipWithVariances arg c tl tl' where
  arg Covariant t t' = intersect t t'
  arg Invariant t t' = equal t t' >. Just t
intersect (TyFun f) (TyFun f') = return (
  if f == f' then Just (TyFun f)
  else Nothing) -- intersect is indeterminant
intersect TyVoid _ = return (Just TyVoid)
intersect _ TyVoid = return (Just TyVoid)
intersect x y = typeMismatch x "&" y

intersectTrans :: Trans -> Trans -> Maybe Trans
intersectTrans tr tr'
  | tr == tr' = Just tr
  | otherwise = Nothing

-- |The equivalent of 'intersect' for lists.  The two lists must have the same size.
--
-- If we come across an indeterminate value early in the list, we still process the rest
-- of this in case we find a clear failure.
_intersectList :: TypeMonad m => [TypeVal] -> [TypeVal] -> m (Maybe [TypeVal])
_intersectList tl tl'
  | Just tt <- zipCheck tl tl' = mapM (uncurry intersect) tt >.= sequence
  | otherwise = typeMismatchList tl "&" tl'

-- |@subset s t@ tries to turn @t@ into @s@ via variable substitutions,
-- but not the other way round.  In other words, subset succeeds if it finds
-- a variable substituion M s.t. S(s) <= S(t|M).
--
-- Note that the occurs check is unnecessary here due to directedness.  In
-- particular, all constraint bindings are of the form v -> t, where t is a TypeVal.
-- Since TypeVal contains no type variables, the occurs check succeeds trivially.
--
-- Operationally, @subset x y@ answers the question \"Can we pass an x to a
-- function that takes y?\"  As an example, @subset Void x@ always succeeds
-- since the hypothesis is vacuously true: there are no values of type Void.
--
-- The order in which subtypes are unified must be adaptive in the presence of
-- function type sets.  For example, in subset (Negate, Int) (a -> Int, a),
-- the value of \"a\" must be determined from the second part of the tuple before
-- the function part can be checked.  To handle this, subset' produces a list
-- of indeterminate subcomputations as it runs, and subsetFix iterates on this
-- until a fixed point is reached.
--
-- The return value of subset is either Right env, indicating success, or
-- Left vars, which means that the result is indeterminate due to the
-- contravariant variables vars.
subset :: TypeMonad m => TypeVal -> TypePat -> m (Either [Var] TypeEnv)
subset t t' = runEnv $ subset' t t' >>= subsetFix Map.empty

-- A pair of function types that need to rerun through subsetFun'.
-- If the first entry is Nothing, the pair must be rerun unconditionally.
-- If the pair is Just env, it must be rerun if any of the constraints
-- referenced referenced by env have changed.
data Leftover
  = Incomplete [TypeFun TypeVal]  [TypeFun TypePat]
  | Complete TypeEnv [TypeFun TypeVal] [TypeFun TypePat]
type Leftovers = [Leftover]

type EnvM m a = StateT Constraints m a
type Env m = EnvM m Leftovers

instance TypeMonad m => TypeMonad (StateT Constraints m) where
  typeApply t = lift . typeApply t

instance TypeSuccess [Leftover] where
  typeSuccess = []
  typeConcat = concat

runEnv :: Monad m => EnvM m (Either [Var] TypeEnv) -> m (Either [Var] TypeEnv)
runEnv m = evalStateT m Map.empty

-- Iterate subset checking until all leftovers are resolved or we reach a
-- fixpoint.  If all leftovers are resolved, we return Right env (success).
-- If we reach a fixpoint first, we return Left vars, where vars are the
-- contravariant vars which prevented leftovers from being resolved.
subsetFix :: TypeMonad m => Constraints -> Leftovers -> EnvM m (Either [Var] TypeEnv)
subsetFix prev leftovers = do
  env <- get
  if prev == env || List.null leftovers
    then return $ case concatMap contravariantVars leftovers of -- reached fixpoint without exhausing leftovers
      [] -> Right (Map.map snd env) -- no incomplete leftovers
      vars -> Left vars
    else subsetFix env =<< sequenceS (map step leftovers) where
  step (Incomplete f f') = subsetFun' f f'
  step (Complete env f f') = get >>= \cnstrs ->
    if any (changed cnstrs) (Map.toList env) then subsetFun' f f' else success
  changed cnstrs (v,t) = let Just (_,t') = Map.lookup v cnstrs in t /= t'
  contravariantVars :: Leftover -> [Var]
  contravariantVars (Incomplete _ fl') = filter (\v -> Map.notMember v prev) (concatMap fun fl') where
    fun (FunArrow _ s _) = freeVars s
    fun (FunClosure _ _) = []
  contravariantVars _ = []

constrain :: TypeMonad m => Var -> ConstraintOp -> TypeVal -> Env m
constrain v op t = success << c op =<< Map.lookup v =.< get where
  c op Nothing = set op t
  c Superset (Just (Superset,t')) = set Superset =<< lift (union t t')
  c Equal    (Just (Superset,t')) = lift (subset'' t' t) >> set Equal t
  c Superset (Just (Equal,t')) = lift (subset'' t t')
  c Equal    (Just (Equal,t')) = lift (equal t t')
  set op t = modify (Map.insert v (op,t))

subset' :: forall m. TypeMonad m => TypeVal -> TypePat -> Env m
subset' (TyStatic (TV x _)) y = subset' x y
subset' t (TsVar v) = constrain v Superset t
subset' (TyCons c tl) (TsCons c' tl') = do
  (c,tl,tl') <- unifyCons c tl c' tl'
  sequenceS =<< zipWithVariances (\v t -> return . arg v t) c tl tl' where
  arg :: Variance -> TypeVal -> TypePat -> Env m
  arg Covariant t t' = subset' t t'
  arg Invariant t t' = equal' t t'
subset' (TyFun f) (TsFun f') = subsetFun' f f'
subset' TyVoid _ = success
subset' x y = typeMismatch x "<=" y

equal' :: TypeMonad m => TypeVal -> TypePat -> Env m
equal' (TyStatic (TV x _)) y = equal' x y
equal' t (TsVar v) = constrain v Equal t
equal' (TyCons c tl) (TsCons c' tl') = do
  (c,tl,tl') <- unifyCons c tl c' tl'
  sequenceS =<< zipWithVariances (\_ t -> return . equal' t) c tl tl'
equal' (TyFun f) (TsFun f') = equalFun' f f'
equal' TyVoid TsVoid = success
equal' x y = typeMismatch x "==" y

-- |Same as 'subset'', but the first argument is a type.
-- subset s t succeeds if S(s) <= S(t).
subset'' :: TypeMonad m => TypeVal -> TypeVal -> m ()
subset'' (TyCons c tl) (TyCons c' tl') = do
  (_,tl,tl') <- unifyCons c tl c' tl'
  subsetList'' tl tl'
subset'' (TyFun f) (TyFun f') = subsetFun'' f f'
subset'' (TyStatic (TV x _)) y = subset'' x y
subset'' TyVoid _ = success
subset'' x y = typeMismatch x "<=" y

subsetTrans :: Trans -> Trans -> Bool
subsetTrans = (==)

equalTrans :: Trans -> Trans -> Bool
equalTrans = (==)

subsetTrans' :: (TypeMonad m, TypeSuccess r) => Trans -> Trans -> m r
subsetTrans' tr tr'
  | subsetTrans tr tr' = success
  | otherwise = typeMismatch tr "<=" tr'

equalTrans' :: (TypeMonad m, TypeSuccess r) => Trans -> Trans -> m r
equalTrans' tr tr'
  | equalTrans tr tr' = success
  | otherwise = typeMismatch tr "==" tr'

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
subsetFun' :: TypeMonad m => [TypeFun TypeVal] -> [TypeFun TypePat] -> Env m
subsetFun' fl fl' = sequenceS (map (fun fl') fl) where
  fun fl' f
    | List.elem (singleton f) fl' = success -- succeed if f appears in fl'
  fun (FunArrow tr' s' t':_) f = do
    cnstrs <- get
    let vars = freeVars s'
        cl = mapM (\v -> Map.lookup v cnstrs) vars
    case cl of
      Nothing -> return [Incomplete fl fl'] -- at least one variable is unbound, so try again later
      Just cl -> do
        let env = Map.fromList (zip vars (map snd cl))
            Just s'' = unsingleton' env s'
        (tr, t) <- typeApply (TyFun [f]) s'' 
        sequenceS
          [ return [Complete env fl fl'] -- if anything in env changes, we'll need to redo this pair
          , subsetTrans' tr tr'
          , subset' t t' ]
  fun _ _ = typeMismatch (TyFun fl) "<=" (TsFun fl')

-- TODO: This is implemented only for primitive functions (single entry TypeFun's)
equalFun' :: forall m. TypeMonad m => [TypeFun TypeVal] -> [TypeFun TypePat] -> Env m
equalFun' [FunArrow tr s t] [FunArrow tr' s' t'] = sequenceS [equal' s s', equalTrans' tr tr', equal' t t']
equalFun' [FunClosure v tl] [FunClosure v' tl'] | v == v', length tl == length tl' = sequenceS (zipWith equal' tl tl')
equalFun' x y = typeMismatch (TyFun x) "==" (TsFun y)

-- |Subset for singleton function types.
subsetFun'' :: forall m. TypeMonad m => [TypeFun TypeVal] -> [TypeFun TypeVal] -> m ()
subsetFun'' fl fl' = mapM_ (fun fl') fl where
  fun fl' f | List.elem f fl' = success -- succeed if f appears in fl'
  fun (FunArrow tr' s' t':_) f = do
    (tr, t) <- typeApply (TyFun [f]) s'
    sequenceS
      [ subsetTrans' tr tr'
      , subset'' t t' ]
  fun _ _ = typeMismatch (TyFun fl) "<=" (TyFun fl')

-- |The equivalent of 'subset' for lists.  To succeed, the second argument must
-- be at least as long as the first (think of the first as being the types of
-- values passed to a function taking the second as arguments).
subsetList :: TypeMonad m => [TypeVal] -> [TypePat] -> m (Either [Var] TypeEnv)
subsetList tl tl' = runEnv $ subsetList' tl tl' >>= subsetFix Map.empty

subsetList' :: TypeMonad m => [TypeVal] -> [TypePat] -> Env m
subsetList' tl tl'
  | length tl <= length tl' = sequenceS $ zipWith subset' tl tl'
  | otherwise = typeMismatchList tl "<=" tl'

-- |Same as 'subsetList'', but for 'TypeVal' instead of 'TypePat'
subsetList'' :: TypeMonad m => [TypeVal] -> [TypeVal] -> m ()
subsetList'' tl tl'
  | length tl <= length tl' = sequenceS $ zipWith subset'' tl tl'
  | otherwise = typeMismatchList tl "<=" tl'

-- |Check whether one typeset list is a specialization of another.  Note that
-- 'specialization' is very different from 'subset' in that it ignores the
-- variances of type arguments and some details of function types.
--
-- Since this function is used only for overload decisions, the soundness of
-- type system does not depend on its correctness.  This is why it is safe to
-- ignore the covariant/invariant distinction.
--
-- In order to disambiguate overloads in the presence of type constructor
-- coersions, we treat every other type constructor as a specialization of
-- Type t.  TODO: This is rather a hack.
_specialization :: TypePat -> TypePat -> Bool
_specialization t t' = isJust (specialization' t t' Map.empty)

specialization' :: TypePat -> TypePat -> Map Var TypePat -> Maybe (Map Var TypePat)
specialization' t (TsVar v') env =
  case Map.insertLookupWithKey (\_ _ t -> t) v' t env of
    (Just t2, _) | t2 /= t -> Nothing
    (_, env) -> Just env
specialization' (TsCons c tl) (TsCons c' tl') env | c == c' = specializationList' tl tl' env
specialization' (TsCons _ _) (TsCons c _) env | c == datatypeType = Just env
specialization' (TsFun f) (TsFun f') env = specializationFuns' f f' env
specialization' _ _ _ = Nothing

specializationList :: [TypePat] -> [TypePat] -> Bool
specializationList tl tl' = isJust (specializationList' tl tl' Map.empty)

specializationList' :: [TypePat] -> [TypePat] -> Map Var TypePat -> Maybe (Map Var TypePat)
specializationList' tl tl' env = List.foldl' (>>=) (return env) =<< zipWithCheck specialization' tl tl'

-- Succeed if for each right-hand function we can find some left-hand function that specializes it
specializationFuns' :: [TypeFun TypePat] -> [TypeFun TypePat] -> Map Var TypePat -> Maybe (Map Var TypePat)
specializationFuns' fl fl' env = List.foldl' (>>=) (return env) (map right fl') where
  right f' env = msum (map (\f -> spec f f' env) fl)
  spec f f' | f == f' = Just
  spec (FunClosure _ _) (FunArrow _ _ _) = Just -- treat closures as specializations of all arrows
  spec (FunArrow _ _ t) (FunArrow _ _ t') = specialization' t t'
  spec _ (FunClosure _ _) = const Nothing
