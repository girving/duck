{-# LANGUAGE PatternGuards, FlexibleInstances, ScopedTypeVariables, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances #-}
-- | Duck Types

module Type
  ( Type(..)
  , TypeSet(..)
  , TypeFun(..)
  , Trans(..)
  , TransType, TypeArg, TypeSetArg
  , TypeEnv
  , transType
  , typeArg
  , argType
  , subset
  , subset''
  , subsetList
  , subsetList''
  , subsetListSkolem
  , union
  , unionList
  , subst
  , substVoid
  , occurs
  , singleton
  , unsingleton
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
  | TsTrans !Trans !TypeSet -- ^ a (temporary) transparent macro transformer type
  deriving (Eq, Ord, Show)

-- |Possible kinds of type macro transformers.
data Trans 
  = Delayed -- :: Delay
  deriving (Eq, Ord, Show)

type TransType t = (Maybe Trans, t)
type TypeArg = TransType Type
type TypeSetArg = TransType TypeSet

type TypeEnv = Map Var Type

-- |Constraints represent constraints on type variables in a typeset
-- or list of typesets.  An entry x -> op t means the final type of x must
-- satisfy S(x) op S(t).
data ConstraintOp = Equal | Superset deriving (Eq)
type Constraints = Map Var (ConstraintOp, Type)

freeze :: Constraints -> TypeEnv
freeze = Map.map snd

-- |The type of functions which say how to apply closure types to types
type Apply m = Type -> Type -> m Type

transType :: Trans -> Type -> Type
transType Delayed t = TyFun (TypeFun [(TyCons (V "()") [],t)] [])

typeArg :: TypeSet -> TypeSetArg
typeArg (TsTrans c t) = (Just c, t)
typeArg t = (Nothing, t)

argType :: (Maybe Trans, Type) -> Type
argType (Nothing, t) = t
argType (Just c, t) = transType c t

-- |@z <- union x y@ means that a value of type x or y can be safely viewed as
-- having type z.  Viewed as sets, this means S(z) >= union S(x) S(y), where
-- equality holds if the union of values can be exactly represented as a type.
--
-- The first argument says how to apply closure types to types.
union :: MonadMaybe m => Apply m -> Type -> Type -> m Type
union apply (TyCons c tl) (TyCons c' tl') | c == c' = TyCons c =.< unionList apply tl tl'
union apply (TyFun f) (TyFun f') = TyFun =.< unionFun apply f f'
union _ TyVoid t = return t
union _ t TyVoid = return t
union _ _ _ = nothing

-- |The equivalent of 'union' for lists.  The two lists must have the same size.
unionList :: MonadMaybe m => Apply m -> [Type] -> [Type] -> m [Type]
unionList _ [] [] = return []
unionList apply (t:tl) (t':tl') = do
  t'' <- union apply t t'
  tl'' <- unionList apply tl tl'
  return (t'':tl'')
unionList _ _ _ = nothing

-- |Union two type functions.  Except in special cases, this means unioning the lists.
unionFun :: MonadMaybe m => Apply m -> TypeFun Type -> TypeFun Type -> m (TypeFun Type)
unionFun apply (TypeFun al cl) (TypeFun al' cl') = do
  al'' <- reduceArrows apply (al++al')
  return $ TypeFun (List.sort al'') (merge cl cl')

-- |Given a union list of arrow types, attempt to reduce them into a
-- smaller equivalent list.  This can either successfully reduce, do nothing,
-- or fail (detect that the union is impossible).
reduceArrows :: MonadMaybe m => Apply m -> [(Type,Type)] -> m [(Type,Type)]
reduceArrows _ [] = return []
reduceArrows apply ((s,t):al) = do
  r <- reduce [] al
  case r of
    Nothing -> ((s,t) :) =.< reduceArrows apply al
    Just al -> reduceArrows apply al -- keep trying, maybe we can reduce more
  where
  reduce _ [] = return Nothing
  reduce prev (a@(s',t') : next) = do
    ss <- intersect apply s s' -- function arguments are contravariant, so intersect
    case ss of
      Nothing -> reduce (a:prev) next
      Just ss -> do
        tt <- union apply t t' -- return values are covariant, so union 
        return $ Just $ (ss,tt) : reverse prev ++ next

-- |@z <- intersect x y@ means that a value of type z can be safely viewed as
-- having type x and type y.  Viewed as sets, S(z) <= intersect S(x) S(y).
--
-- Not all intersections are representable in the case of function types, so
-- intersect can either succeed (the result is representable), fail
-- (intersection is definitely invalid), or be indeterminant (we don't know).
-- The indeterminate case returns Nothing.
intersect :: MonadMaybe m => Apply m -> Type -> Type -> m (Maybe Type)
intersect apply (TyCons c tl) (TyCons c' tl') | c == c' = fmap (TyCons c) =.< intersectList apply tl tl'
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
intersectList :: MonadMaybe m => (Type -> Type -> m Type) -> [Type] -> [Type] -> m (Maybe [Type])
intersectList _ [] [] = return (Just [])
intersectList apply (t:tl) (t':tl') = do
  t'' <- intersect apply t t'
  tl'' <- intersectList apply tl tl'
  return (case (t'',tl'') of
    (Just t,Just tl) -> Just (t:tl)
    _ -> Nothing)
intersectList _ _ _ = nothing

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
subset :: MonadMaybe m => Apply m -> Type -> TypeSet -> m (TypeEnv, Leftovers)
subset apply t t' = subset' apply Map.empty t t' >>= subsetFix apply Map.empty >.= first freeze

type Leftover = (TypeFun Type, TypeFun TypeSet)
type Leftovers = [Leftover]

subsetFix :: MonadMaybe m => Apply m -> Constraints -> (Constraints, Leftovers) -> m (Constraints, Leftovers)
subsetFix _ _ r@(_, []) = return r -- finished leftovers, so done
subsetFix _ prev r@(env, _) | prev == env = return r -- reached fixpoint without exhausing leftovers
subsetFix apply _ (env, leftovers) = subsetFix apply env =<< foldM step (env, []) leftovers where
  step (env, leftovers) (f,f') = do
    (env, l) <- subsetFun' apply env f f'
    return (env, l ++ leftovers)

subset' :: MonadMaybe m => Apply m -> Constraints -> Type -> TypeSet -> m (Constraints, Leftovers)
subset' apply env t (TsVar v) =
  case Map.lookup v env of
    Nothing -> return (Map.insert v (Superset,t) env, [])
    Just (Superset,t') -> union apply t t' >.= \t'' -> (Map.insert v (Superset,t'') env, [])
    Just (Equal,t') -> subset'' apply t t' >. (env, [])
subset' apply env (TyCons c tl) (TsCons c' tl') | c == c' = subsetList' apply env tl tl'
subset' apply env (TyFun f) (TsFun f') = subsetFun' apply env f f'
subset' _ env TyVoid _ = return (env,[])
subset' _ _ _ _ = nothing

-- |Same as 'subset'', but the first argument is a type.
-- subset s t succeeds if S(s) <= S(t).
subset'' :: MonadMaybe m => Apply m -> Type -> Type -> m ()
subset'' apply (TyCons c tl) (TyCons c' tl') | c == c' = subsetList'' apply tl tl'
subset'' apply (TyFun f) (TyFun f') = subsetFun'' apply f f'
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
subsetFun' :: forall m. MonadMaybe m => Apply m -> Constraints -> TypeFun Type -> TypeFun TypeSet -> m (Constraints, Leftovers)
subsetFun' apply env ft@(TypeFun al cl) ft'@(TypeFun al' cl') = do
  seq env [] $ map (arrow al' cl') al ++ map (closure al' cl') cl
  where
  seq :: Constraints -> Leftovers -> [Constraints -> m (Constraints, Leftovers)] -> m (Constraints, Leftovers)
  seq env leftovers [] = return (env,leftovers)
  seq env leftovers (m:ml) = do
    (env,l1) <- m env
    (env,l2) <- seq env leftovers ml
    return (env,l1++l2)

  -- For each var in the list, change any Superset constraints to Equal.
  freezeVars :: Constraints -> [Var] -> Constraints
  freezeVars = foldl (\env v -> Map.adjust (first (const Equal)) v env)

  arrow :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Type,Type) -> Constraints -> m (Constraints, Leftovers)
  arrow al' _ f env
    | List.elem (singleton f) al' = return (env,[]) -- succeed if f appears in al'
  arrow ((s',t'):_) _ f env = do
    case unsingleton' env s' of
      Nothing -> return (env,[(ft,ft')])
      Just s'' -> do
        t <- apply (TyFun (TypeFun [f] [])) s''
        let env' = freezeVars env (vars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' apply env' t t'
  arrow [] _ _ _ = nothing

  closure :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Var,[Type]) -> Constraints -> m (Constraints, Leftovers)
  closure _ fl' f env
    | List.elem (singleton f) fl' = return (env,[]) -- succeed if f appears in fl'
  closure ((s',t'):_) _ f env = do
    case unsingleton' env s' of
      Nothing -> return (env,[(ft,ft')])
      Just s'' -> do
        t <- apply (TyFun (TypeFun [] [f])) s''
        let env' = freezeVars env (vars s') -- We're about to feed these vars to apply, so they'll become rigid
        subset' apply env' t t'
  closure [] _ _ _ = nothing

-- |Subset for singleton function types.
subsetFun'' :: forall m. MonadMaybe m => Apply m -> TypeFun Type -> TypeFun Type -> m ()
subsetFun'' apply (TypeFun al cl) (TypeFun al' cl') = do
  mapM_ (arrow al' cl') al
  mapM_ (closure al' cl') cl
  where
  arrow :: [(Type,Type)] -> [(Var,[Type])] -> (Type,Type) -> m ()
  arrow al' _ a | List.elem a al' = success -- succeed if a appears in al'
  arrow ((s',t'):_) _ (s,t) = do
    subset'' apply s' s -- contravariant
    subset'' apply t t' -- covariant
  arrow [] _ _ = nothing -- arrows are never considered as general as closures

  closure :: [(Type,Type)] -> [(Var,[Type])] -> (Var,[Type]) -> m ()
  closure _ fl' f | List.elem f fl' = success -- succeed if f appears in fl'
  closure ((s',t'):_) _ f = do
    t <- apply (TyFun (TypeFun [] [f])) s'
    subset'' apply t t'
  closure [] _ _ = nothing

-- |The equivalent of 'subset' for lists.  To succeed, the second argument must
-- be at least as long as the first (think of the first as being the types of
-- values passed to a function taking the second as arguments).
subsetList :: MonadMaybe m => Apply m -> [Type] -> [TypeSet] -> m (TypeEnv, Leftovers)
subsetList apply tl tl' = subsetList' apply Map.empty tl tl' >>= subsetFix apply Map.empty >.= first freeze

subsetList' :: MonadMaybe m => Apply m -> Constraints -> [Type] -> [TypeSet] -> m (Constraints, Leftovers)
subsetList' _ env [] _ = return (env,[])
subsetList' apply env (t:tl) (t':tl') = do
  (env,l1) <- subset' apply env t t'
  (env,l2) <- subsetList' apply env tl tl'
  return (env, l1 ++ l2)
subsetList' _ _ _ _ = nothing

-- |Same as 'subsetList'', but for Type instead of TypeSet
subsetList'' :: MonadMaybe m => Apply m -> [Type] -> [Type] -> m ()
subsetList'' _ [] _ = success
subsetList'' apply (t:tl) (t':tl') = do
  subset'' apply t t'
  subsetList'' apply tl tl'
subsetList'' _ _ _ = nothing

-- |'subsetList' for the case of two type sets.  Here the two sets of variables are
-- considered to come from separate namespaces.  To make this clear, we implement
-- this function using skolemization, by turning all variables in the second
-- TypeSet into TyConses.
subsetListSkolem :: MonadMaybe m => Apply m -> [TypeSet] -> [TypeSet] -> m ()
subsetListSkolem apply x y = subsetList apply (map skolemize x) y >. ()

-- |Type environment substitution
subst :: TypeEnv -> TypeSet -> TypeSet
subst env (TsVar v)
  | Just t <- Map.lookup v env = singleton t
  | otherwise = TsVar v
subst env (TsCons c tl) = TsCons c (map (subst env) tl)
subst env (TsFun f) = TsFun (substFun env f)
subst env (TsTrans c t) = TsTrans c (subst env t)
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
substVoid env (TsTrans c t) = transType c (substVoid env t)
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
occurs env v (TsTrans _ t) = occurs env v t
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
unsingleton' env (TsTrans c t) = transType c =.< unsingleton' env t
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
skolemize :: TypeSet -> Type
skolemize (TsVar v) = TyCons v [] -- skolemization
skolemize (TsCons c tl) = TyCons c (map skolemize tl)
skolemize (TsFun f) = TyFun (skolemizeFun f)
skolemize (TsTrans _ t) = skolemize t
skolemize TsVoid = TyVoid

skolemizeFun :: TypeFun TypeSet -> TypeFun Type
skolemizeFun (TypeFun al cl) = TypeFun (map arrow al) (map closure cl) where
  arrow (s,t) = (skolemize s, skolemize t)
  closure (f,tl) = (f, map skolemize tl)

-- |Find the set of free variables in a typeset
vars :: TypeSet -> [Var]
vars (TsVar v) = [v]
vars (TsCons _ tl) = concatMap vars tl
vars (TsFun f) = varsFun f
vars (TsTrans _ t) = vars t
vars TsVoid = []

varsFun :: TypeFun TypeSet -> [Var]
varsFun (TypeFun al cl) = concatMap arrow al ++ concatMap closure cl where
  arrow (s,t) = vars s ++ vars t
  closure (_,tl) = concatMap vars tl

-- |If leftovers remain after unification, this function explains which
-- variables caused the problem.
contravariantVars :: Leftovers -> [Var]
contravariantVars = concatMap cv where
  cv (_, TypeFun al _) = concatMap (vars . fst) al

showContravariantVars :: Leftovers -> String
showContravariantVars leftovers = case contravariantVars leftovers of
  [v] -> "variable "++pshow v
  vl -> "variables "++concat (List.intersperse ", " (map (show . pretty) vl))
 
-- Pretty printing

instance Pretty TypeSet where
  pretty' (TsVar v) = pretty' v
  pretty' (TsCons t []) = pretty' t
  pretty' (TsCons t tl) | istuple t = (2, hcat $ List.intersperse (pretty ", ") $ map (guard 3) tl)
  pretty' (TsCons t tl) = (50, guard 50 t <+> hsep (map (guard 51) tl))
  pretty' (TsFun f) = pretty' f
  pretty' (TsTrans c t) = (1, pretty (show c) <+> guard 2 t)
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

instance Pretty t => Pretty (Maybe Trans, t) where
  pretty' (Nothing, t) = pretty' t
  pretty' (Just c, t) = (1, pretty (show c) <+> guard 2 t)
