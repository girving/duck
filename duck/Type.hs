{-# LANGUAGE PatternGuards, FlexibleInstances, ScopedTypeVariables #-}
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
  , unify
  , unify''
  , unifyList
  , unifyList''
  , unifyListSkolem
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
-- The unification operation below corresponds to a subset test;
-- "unify a b" answers the question "Can we pass b to (a -> ...)?", so
-- "unify a b" succeeds iff "b" is a subset of "a".
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

-- |@unify s t@ tries to turn @s@ into @t@ via variable substitutions,
-- but not the other way round.  In other words, unify succeeds if it finds
-- a variable substituion M s.t. S(t) <= S(s|M).
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

type Leftover = (TypeFun TypeSet, TypeFun Type)
type Leftovers = [Leftover]

unifyFix :: MonadMaybe m => Apply m -> TypeEnv -> (TypeEnv, Leftovers) -> m (TypeEnv, Leftovers)
unifyFix _ _ r@(_, []) = return r -- finished leftovers, so done
unifyFix _ prev r@(env, _) | prev == env = return r -- reached fixpoint without exhausing leftovers
unifyFix apply _ (env, leftovers) = unifyFix apply env =<< foldM step (env, []) leftovers where
  step (env, leftovers) (f,f') = do
    (env, l) <- unifyFun' apply env f f'
    return (env, l ++ leftovers)

unify' :: MonadMaybe m => Apply m -> TypeEnv -> TypeSet -> Type -> m (TypeEnv, Leftovers)
unify' apply env (TsVar v) t =
  case Map.lookup v env of
    Nothing -> return (Map.insert v t env, [])
    Just t' -> union apply t t' >.= \t'' -> (Map.insert v t'' env, [])
unify' apply env (TsCons c tl) (TyCons c' tl') | c == c' = unifyList' apply env tl tl'
unify' apply env (TsFun f) (TyFun f') = unifyFun' apply env f f'
unify' _ env _ TyVoid = return (env,[])
unify' _ _ _ _ = nothing

-- |Same as 'unify'', but the first argument is a type.
-- unify s t succeeds if S(t) <= S(s).
unify'' :: MonadMaybe m => Apply m -> Type -> Type -> m ()
unify'' apply (TyCons c tl) (TyCons c' tl') | c == c' = unifyList'' apply tl tl'
unify'' apply (TyFun f) (TyFun f') = unifyFun'' apply f f'
unify'' _ _ TyVoid = success
unify'' _ _ _ = nothing

-- |Unify for function types
--
-- We use the following rules:
--     unify (union_f f) (union_f' f')
--        = union_f' intersect_f (unify f f')
--     unify (a -> b) (c -> d) = unify c a -> unify b d
--     unify (a -> b) closure = a -> unify b (closure a)
--     unify closure (a -> b) = fail
-- TODO: Currently all we know is that m is a MonadMaybe, and therefore we
-- lack the ability to do speculative computation and rollback.  Therefore,
-- "intersect" currently means ignore all but the first entry.
unifyFun' :: forall m. MonadMaybe m => Apply m -> TypeEnv -> TypeFun TypeSet -> TypeFun Type -> m (TypeEnv, Leftovers)
unifyFun' apply env ft@(TypeFun al cl) ft'@(TypeFun al' cl') = do
  seq env [] $ map (arrow al cl) al' ++ map (closure al cl) cl'
  where
  seq :: TypeEnv -> Leftovers -> [TypeEnv -> m (TypeEnv, Leftovers)] -> m (TypeEnv, Leftovers)
  seq env leftovers [] = return (env,leftovers)
  seq env leftovers (m:ml) = do
    (env,l1) <- m env
    (env,l2) <- seq env leftovers ml
    return $ (env,l1++l2)

  arrow :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Type,Type) -> TypeEnv -> m (TypeEnv, Leftovers)
  arrow al _ (s',t') env
    | s'' <- singleton s'
    , t'' <- singleton t'
    , List.elem (s'',t'') al = return (env,[]) -- succeed if (s',t') appears in al
  arrow ((s,t):_) _ (s',t') env = do
    case unsingleton' env s of
      Nothing -> return (env,[(ft,ft')])
      Just s -> do
        unify'' apply s' s -- reverse arguments for contravariance
        unify' apply env t t' -- back to covariant
  arrow [] _ _ _ = nothing -- arrows are never considered as general as closures

  closure :: [(TypeSet,TypeSet)] -> [(Var,[TypeSet])] -> (Var,[Type]) -> TypeEnv -> m (TypeEnv, Leftovers)
  closure _ fl f' env
    | f'' <- second (map singleton) f'
    , List.elem f'' fl = return (env,[]) -- succeed if f' appears in fl
  closure ((s,t):_) _ f' env = do
    case unsingleton' env s of
      Nothing -> return (env,[(ft,ft')])
      Just s -> do
        t' <- apply (TyFun (TypeFun [] [f'])) s
        unify' apply env t t'
  closure [] _ _ _ = nothing

-- |Unify for singleton function types.
unifyFun'' :: forall m. MonadMaybe m => Apply m -> TypeFun Type -> TypeFun Type -> m ()
unifyFun'' apply (TypeFun al cl) (TypeFun al' cl') = do
  mapM_ (arrow al cl) al'
  mapM_ (closure al cl) cl'
  where
  arrow :: [(Type,Type)] -> [(Var,[Type])] -> (Type,Type) -> m ()
  arrow al _ a' | List.elem a' al = success -- succeed if a' appears in al
  arrow ((s,t):_) _ (s',t') = do
    unify'' apply s' s -- contravariant
    unify'' apply t t' -- covariant
  arrow [] _ _ = nothing -- arrows are never considered as general as closures

  closure :: [(Type,Type)] -> [(Var,[Type])] -> (Var,[Type]) -> m ()
  closure _ fl f' | List.elem f' fl = success -- succeed if f' appears in fl
  closure ((s,t):_) _ f' = do
    t' <- apply (TyFun (TypeFun [] [f'])) s
    unify'' apply t t'
  closure [] _ _ = nothing

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
singleton :: Type -> TypeSet
singleton (TyCons c tl) = TsCons c (map singleton tl)
singleton (TyFun f) = TsFun (singletonFun f)
singleton TyVoid = TsVoid

singletonFun :: TypeFun Type -> TypeFun TypeSet
singletonFun (TypeFun al cl) = TypeFun (map arrow al) (map closure cl) where
  arrow (s,t) = (singleton s, singleton t)
  closure (f,tl) = (f, map singleton tl)
 
-- |Convert a singleton typeset to a type if possible
unsingleton :: TypeSet -> Maybe Type
unsingleton = unsingleton' Map.empty

unsingleton' :: TypeEnv -> TypeSet -> Maybe Type
unsingleton' env (TsVar v) | Just t <- Map.lookup v env = return t
unsingleton' _ (TsVar _) = nothing
unsingleton' env (TsCons c tl) = TyCons c =.< mapM (unsingleton' env) tl
unsingleton' env (TsFun f) = TyFun =.< unsingletonFun' env f
unsingleton' env (TsTrans c t) = transType c =.< unsingleton' env t
unsingleton' _ TsVoid = return TyVoid

unsingletonFun' :: TypeEnv -> TypeFun TypeSet -> Maybe (TypeFun Type)
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

-- |If leftovers remain after unification, this function explains which
-- variables caused the problem.
contravariantVars :: Leftovers -> [Var]
contravariantVars = concatMap cv where
  cv (TypeFun al _, _) = concatMap (vars . fst) al
  vars (TsVar v) = [v]
  vars (TsCons _ tl) = concatMap vars tl
  vars (TsFun f) = varsFun f
  vars (TsTrans _ t) = vars t
  vars TsVoid = []
  varsFun (TypeFun al cl) = concatMap arrow al ++ concatMap closure cl where
    arrow (s,t) = vars s ++ vars t
    closure (_,tl) = concatMap vars tl

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
