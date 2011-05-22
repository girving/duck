{-# LANGUAGE PatternGuards, ScopedTypeVariables #-}
-- | Duck type inference
--
-- Algorithm discussion:
--
-- The state of the type inference algorithm consists of
--
-- (1) A set of function type primitives (functors) representing maps from types to types.
--
-- (2) A map from variables to (possibly primitive) types.
--
-- (3) A set of in-progress type applications to compute fixed points in the case of recursion.

module Infer
  ( prog
  , expr
  , atom
  , cons
  , spec
  , apply
  , isTypeType
  , isTypeDelay
  , staticFunction
  -- * Environment access
  , lookupDatatype
  , lookupCons
  , lookupOver
  ) where

import Prelude hiding (lookup)

import Control.Monad
import qualified Control.Monad.Reader as Reader
import Control.Monad.State
import Data.Either
import Data.Function
import Data.List hiding (lookup, union)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import Util
import Pretty hiding (guard)
import Var
import SrcLoc
import Type
import TypeSet
import Prims
import Lir hiding (union)
import InferMonad
import qualified Ptrie
import qualified Base
import Memory
import PrettyLir ()

-- Some aliases for documentation purposes

type Locals = TypeEnv

-- Utility functions

-- |Insert an overload into the table.  The first argument is meant to indicate whether this is a final resolution, or a temporary one before fixpoint convergance.
insertOver :: Bool -> Var -> [TransType TypeVal] -> Overload TypeVal -> Infer ()
insertOver _final f a o = do
  --debugInfer $ "recorded" <:> prettyap f a <+> '=' <+> overRet o
  modify $ Ptrie.mapInsert f a o

partialOver :: Var -> [Trans] -> [TypeVal] -> Overload TypeVal
partialOver f tt tl = Over noLoc (zip tt tl) (typeClosure f tl) [] Nothing

-- |Lookup an overload from the table, or make one if it's partial
lookupOver :: Var -> [TypeVal] -> Infer (Maybe (Overload TypeVal))
lookupOver f tl = (uncurry over .=< uncurry (fmap . (,)) . Ptrie.lookup tl <=< Map.lookup f) =.< get where
  over tt = fromMaybe (partialOver f tt tl) . Ptrie.unLeaf

lookupDatatype :: SrcLoc -> TypeVal -> Infer [(Loc CVar, [TypeVal])]
lookupDatatype loc (TyCons d [t]) | d == datatypeType = case t of
  TyCons c tl -> return [(L noLoc (dataName c), map typeType tl)]
  TyVoid -> return [(L noLoc (V "Void"), [])]
  _ -> inferError loc $ "cannot pattern match on" <+> quoted (typeType t) <> "; matching on function types isn't implemented yet"
lookupDatatype loc (TyCons d types) = case dataInfo d of
  DataAlgebraic conses -> return $ map (second $ map $ substVoid $ Map.fromList $ zip (dataTyVars d) types) conses
  DataPrim _ -> typeError loc ("expected algebraic datatype, got" <+> quoted d)
lookupDatatype loc (TyStatic (Any t _)) = lookupDatatype loc t
lookupDatatype _ TyVoid = return []
lookupDatatype loc t = typeError loc ("expected datatype, got" <+> quoted t)

lookupFunction :: Var -> Infer [Overload TypePat]
lookupFunction f = getProg >>= \prog ->
  case Map.lookup f (progFunctions prog) of
    Just o -> return o
    _ -> inferError noLoc ("unbound function" <+> quoted f)

lookupCons :: [(Loc CVar, [t])] -> CVar -> Maybe [t]
lookupCons cases c = fmap snd (List.find ((c ==) . unLoc . fst) cases)

withGlobals :: GlobalTypes -> Infer [(Var,GlobalType)] -> Infer GlobalTypes
withGlobals g f =
  foldr (uncurry insertVar) g =.< 
    Reader.local (first (\p -> p{ progGlobalTypes = g })) f

-- |Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Infer GlobalTypes
prog = foldM (\g -> withGlobals g . definition) Map.empty . progDefinitions =<< getProg

definition :: Definition -> Infer [(Var,GlobalType)]
definition d@(Def st vl e) =
  withFrame (V $ intercalate "," $ map (\(L _ (V s)) -> s) vl) [] l $ do
  t <- expr st Map.empty l e
  tl <- case (vl,t) of
          (_, TyVoid) -> return $ map (const TyVoid) vl
          ([_],_) -> return [t]
          (_, TyStatic (Any (TyCons c tl) d)) | isDatatypeTuple c, length vl == length tl ->
            return $ zipWith (TyStatic ... Any) tl dl
            where dl = unsafeUnvalConsN (length tl) d
          (_, TyCons c tl) | isDatatypeTuple c, length vl == length tl -> 
            return tl
          ([],_) -> inferError l $ "expected (), got" <+> quoted t
          _ -> inferError l $ "expected" <+> length vl <> "-tuple, got" <+> quoted t
  return $ zipWith3 (\v t i -> (unLoc v,(t,(e,i)))) vl tl $
    case tl of { [_] -> [Nothing] ; _ -> map Just [0..] }
  where l = loc d

isStatic :: TypeVal -> Bool
isStatic (TyStatic{}) = True
isStatic (TyFun fl) = all sf fl where
  sf (FunArrow{}) = False
  sf (FunClosure _ tl) = all isStatic tl
isStatic _ = False

reStatic :: TypeVal -> TypeVal -> TypeVal
reStatic (TyStatic (Any _ d)) t = TyStatic (Any t d)
reStatic _ t = t

expr :: Bool -> Locals -> SrcLoc -> Exp -> Infer TypeVal
expr static env loc e = checkStatic =<< exp e where
  exp (ExpAtom a) = atom static env loc a
  exp (ExpApply e1 e2) = do
    t1 <- exp e1
    st <- staticFunction t1
    t2 <- expr (static || st) env loc e2
    snd =.< apply static loc t1 t2
  exp (ExpLet v e body) = do
    t <- exp e
    expr static (Map.insert v t env) loc body
  exp (ExpCase a pl def) = do
    t <- checkStatic =<< atom static env loc a
    conses <- lookupDatatype loc t
    case t of
      TyVoid -> return TyVoid
      TyStatic tv@(Any _ d) -> do
        let i = unsafeTag d
            (L _ c, tl) = conses !! i
            n = length tl
        case find (\(c',_,_) -> c == c') pl of
          Just (_,vl,e') 
            | length vl == n -> do
              let dl = unsafeUnvalConsN (length tl) d
              expr static (insertVars env vl $ zipWith (TyStatic ... Any) tl dl) loc e'
            | otherwise -> inferError loc $ "arity mismatch in static pattern:" <+> 
              quoted c <+> "expected" <+> a <+> "argument"<>sPlural tl <+>
              "but got" <+> quoted (hsep vl)
          Nothing -> maybe
            (inferError loc ("static pattern match failed: exp =" <+> quoted tv))
            exp def
      t -> do
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        unifyList loc (caseResults ++ defaultResults)
        where
        caseType (c,vl,e') = case lookupCons conses c of
          Just tl | length tl == length vl ->
            expr static (insertVars env vl tl) loc e'
          Just tl ->
            inferError loc $ "arity mismatch in pattern:" <+> 
              quoted c <+> "expected" <+> length tl <+> "argument"<>sPlural tl <+>
              "but got" <+> quoted (hsep vl)
          Nothing ->
            inferError loc ("datatype" <+> quoted t <+> "has no constructor" <+> quoted c)
        defaultType Nothing = return []
        defaultType (Just e') = expr static env loc e' >.= (:[])
  exp (ExpCons d c el) =
    cons static loc d c =<< mapM exp el
  exp (ExpPrim op el) =
    -- TODO: execute if static or non-IO and all args static
    Base.primType loc op =<< mapM exp el
  exp (ExpSpec e ts) =
    spec loc ts e =<< exp e
  exp (ExpLoc l e) = expr static env l e
  checkStatic t
    | not static || isStatic t = return t
    | otherwise = inferError loc $ "non-static value in static expression:" <+> quoted (show e) <+> "=>" <+> quoted (show t)

lookupVariable :: SrcLoc -> Var -> Map Var a -> Infer a
lookupVariable loc v env = 
  maybe 
    (inferError loc $ "unbound variable" <+> quoted v)
    return $ Map.lookup v env

atom :: Bool -> Locals -> SrcLoc -> Atom -> Infer TypeVal
atom False _ _ (AtomVal (Any t _)) = return t
atom True _ _ (AtomVal tv) = return $ TyStatic tv
atom _ env loc (AtomLocal v) = lookupVariable loc v env
atom False _ loc (AtomGlobal v) = fst =.< lookupVariable loc v . progGlobalTypes =<< getProg
atom True _ loc (AtomGlobal v) = do
  (t, (e, i)) <- lookupVariable loc v . progGlobalTypes =<< getProg
  if isStatic t
    then return t
    else maybe return pick i =<< expr True Map.empty loc e
  where
  pick i (TyStatic (Any (TyCons c tl) d)) | isDatatypeTuple c =
    return $ TyStatic $ Any (tl !! i) di
    where di = unsafeUnvalConsNth d i
  pick i (TyCons c tl) | isDatatypeTuple c = -- this is probably an error if not impossible
    return $ tl !! i
  pick _ t = inferError loc $ "expected static tuple, got" <+> t

cons :: Bool -> SrcLoc -> Datatype -> Int -> [TypeVal] -> Infer TypeVal
cons static loc d c args = do
  conses <- case dataInfo d of
    DataAlgebraic conses -> return conses
    DataPrim _ -> typeError loc ("expected algebraic datatype, got" <+> quoted d)
  let (cv,tl) = conses !! c
  tenv <- typeReError loc (quoted cv <+> "expected arguments" <+> quoted (hsep tl) <> ", got" <+> quoted (hsep args)) $
    checkLeftovers noLoc () =<<
    subsetList args tl
  let targs = map (\v -> Map.findWithDefault TyVoid v tenv) (dataTyVars d)
      t = TyCons d targs
  return $ maybe t
    (TyStatic . Any t . valCons c)
    (Control.Monad.guard static >> mapM unStatic args)

spec :: SrcLoc -> TypePat -> Exp -> TypeVal -> Infer TypeVal
spec loc ts e t = do
  tenv <- checkLeftovers loc ("type specification" <+> quoted ts <+> "is invalid") =<<
    (typeReError loc (quoted e <+> "has type" <+> quoted t <> ", which is incompatible with type specification" <+> quoted ts) $
      subset t ts)
  return $ substVoid tenv ts

unify :: SrcLoc -> TypeVal -> TypeVal -> Infer TypeVal
unify loc (TyStatic (Any t1 v1)) (TyStatic (Any t2 v2)) = do
  t <- unify loc t1 t2
  unless (Any t v1 == Any t v2) $ inferError loc $ "indeterminate static values in return"
  return $ TyStatic (Any t v1)
-- if only one static, it's dropped:
unify loc t1 t2 =
  typeReError loc ("failed to unify types" <+> quoted t1 <+> "and" <+> quoted t2) $
    union t1 t2

-- In future, we might want this to produce more informative error messages
unifyList :: SrcLoc -> [TypeVal] -> Infer TypeVal
unifyList loc = foldM1 (unify loc)

apply :: Bool -> SrcLoc -> TypeVal -> TypeVal -> Infer (Trans, TypeVal)
apply _ _ TyVoid _ = return (NoTrans, TyVoid)
apply static loc (TyStatic (Any t _)) t2 = apply static loc t t2
apply static loc (TyFun fl) t2 = do
  (t:tt, l) <- mapAndUnzipM fun fl
  unless (all (t ==) tt) $
    inferError loc ("conflicting transforms applying" <+> quoted fl <+> "to" <+> quoted t2)
  -- FIXME static
  (,) t =.< unifyList loc l
  where
  fun f@(FunArrow t a r) = do
    typeReError loc ("cannot apply" <+> quoted f <+> "to" <+> quoted t2) $
      subset'' t2 a
    return (t, r)
  fun ft@(FunClosure f args) = do
    st <- staticFunction (TyFun [ft])
    let tl = args ++ [if st then t2 else deStatic t2]
    o <- maybe (withFrame f tl loc $ resolve f tl)
      return =<< lookupOver f tl
    debugInfer $ "got" <+> prettyap f tl <+> "=>" <+> o
    r <- if static
      then maybe
        (return $ typeClosure f (args ++ [t2]))
        -- if static we need to reevaluate the whole thing statically to get a static result:
        (withFrame f tl loc .
          expr static (Map.fromList $ zipWith3 
            (\v (t,_) a -> (v, transType (t,a)))
            (overVars o) (overArgs o) (args ++ [t2])) (overLoc o))
        (overBody o)
      else return $ overRet o
    when static $ debugInfer $ "evaled" <+> r
    return (fst $ overArgs o !! length args, r)
apply _ loc t1 t2 = liftM ((,) NoTrans) $
  app Infer.isTypeType appty $
  app Infer.isTypeDelay appdel $
  typeError loc ("cannot apply" <+> quoted t1 <+> "to" <+> quoted t2)
  where
  app t f r = maybe r f =<< t t1
  appty ~(TyCons c tl)
    | length tl < length (dataVariances c) =
      typeType =.< if c == datatypeType then return t2 else do
        r <- isTypeType t2
        case r of
          Just t -> return $ TyCons c (tl++[t])
          _ -> typeError loc ("cannot apply" <+> quoted t1 <+> "to non-type" <+> quoted t2)
    | otherwise = typeError loc ("cannot apply" <+> quoted t1 <+> "to" <+> quoted t2 <> "," <+> quoted c <+> "is already fully applied")
  appdel t = do
    r <- tryError $ subset t2 typeUnit
    case r of
      Right (Right _) -> return t
      _ -> typeError loc ("cannot apply" <+> quoted t1 <+> "to" <+> quoted t2 <> ", can only be applied to" <+> quoted "()")

isTypeC1 :: Datatype -> TypeVal -> Infer (Maybe TypeVal)
isTypeC1 c tt = do
  r <- tryError $ subset tt (TsCons c [TsVar x])
  return $ case r of
    Right (Right env) | Just t <- Map.lookup x env -> Just t
    _ -> Nothing
  where x = V "x"

isTypeType :: TypeVal -> Infer (Maybe TypeVal)
isTypeType = isTypeC1 datatypeType

isTypeDelay :: TypeVal -> Infer (Maybe TypeVal)
isTypeDelay = isTypeC1 datatypeDelay

instance TypeMonad Infer where
  typeApply f = apply False noLoc f

overDesc :: Overload TypePat -> Doc'
overDesc o = o { overBody = Nothing } <+> parens ("at" <+> show (overLoc o))

-- |Given a @<@ comparison function, return the elements not greater than any other
leasts :: (a -> a -> Bool) -> [a] -> [a]
leasts _ [] = []
leasts (<) (x:l)
  | any (< x) l = r
  | otherwise = x:r
  where r = leasts (<) $ filter (not . (x <)) l

-- |Deterine applicable overloads.
-- This information could be cached in the Ptrie.
overload :: Var -> [TypeVal] -> Infer [(Overload TypePat, Either [Var] TypeEnv)]
overload f args = do
  allovers <- lookupFunction f
  let prune o = tryError $ ((,) o) =.< subsetList args (overTypes o)
  pruned <- mapM prune allovers
  case partitionEithers pruned of
    (errs,[]) -> typeError noLoc $
      nestedPunct ':' ("no matching overload for" <+> quoted f <> ", tried") $
        vcat $ zipWith (nestedPunct ':' . overDesc) allovers errs
    (_,os) -> return $ leasts (specializationList `on` overTypes . fst) os

-- |Resolve an overloaded application.  If all overloads are still partially applied, the result will have @overBody = Nothing@ and @overRet = typeClosure@.
resolve :: Var -> [TypeVal] -> Infer (Overload TypeVal)
resolve f args = do
  overs <- overload f args
  let options = vcat $ map (overDesc . fst) overs

  -- determine applicable argument type transform annotations
  tt <- maybe
    (inferError noLoc $ nested ("ambiguous type transforms, possibilities are:") options)
    return $ unique $ map (map fst . take (length args) . overArgs . fst) overs
  let at = zip tt args

  over <- case partition ((length args ==) . length . overVars . fst) overs of
    ([(o,tenv)],[]) -> -- exactly one fully applied option: evaluate
      cache f at o =<< 
        checkLeftovers noLoc ("invalid overload" <+> overDesc o) tenv
    ([],_) -> -- all overloads are still partially applied, so create a closure overload
      return $ partialOver f tt args
    _ | any ((TyVoid ==) . transType) at -> -- ambiguous with void arguments
      return (Over noLoc at TyVoid [] Nothing)
    _ -> -- ambiguous
      inferError noLoc $ nested ("ambiguous overloads for" <+> quoted f <> ", possibilities are:") options

  insertOver True f at over
  return over

-- |Type infer a function call and cache the results
--
-- * TODO: cache currently infers every nonvoid function call at least thrice, regardless of recursion.  Fix this.
--
-- * TODO: we should tweak this so that only intermediate (non-fixpoint) types are recorded into a separate map, so that
-- they can be easily rolled back in SFINAE cases /without/ rolling back complete computations that occurred in the process.
cache :: Var -> [TransType TypeVal] -> Overload TypePat -> TypeEnv -> Infer (Overload TypeVal)
cache f al (Over oloc atypes rt vl ~(Just e)) tenv = do
  s <- get -- fork state to do speculative fixpoint
  r <- fix False TyVoid -- recursive function calls are initially assumed to be void
  put s -- restore state
  r' <- fix True r -- and finalize with correct type
  when (r /= r') $ inferError noLoc "internal error: type convergence failed"
  return (or r)
  where
  tf (r, arg) (_r, a) = (r, reStatic arg $ substVoid tenv a)
  tl = zipWith tf al atypes
  rs = substVoid tenv rt
  or r = Over oloc tl r vl (Just e)
  eval = do
    r <- expr False (Map.fromList (zip vl (map transType tl))) oloc e
    typeReError noLoc ("failed to unify result" <+> quoted r <+>"with return signature" <+> quoted rs) $
      union r rs
  fix final prev = do
    insertOver final f al (or prev)
    r <- eval
    if final || r == prev
      then return r
      else fix final r

checkLeftovers :: Pretty m => SrcLoc -> m -> Either [Var] a -> Infer a
checkLeftovers loc m = either 
  (\l -> inferError loc (m <> "; cannot overload on contravariant variable"<>sPlural l <+> quoted (hsep l)))
  return

-- |Determine if a given type, when used as a function, takes a static argument
-- TODO: improve error message, and ideally avoid the re-overload (should be in ptrie during exec)
staticFunction :: TypeVal -> Infer Bool
staticFunction (TyFun fl) = maybe (inferError noLoc "ambiguous staticness") return . unique . concat =<< mapM sf fl where
  sf (FunArrow tr _ _) = return $ [Static == tr]
  sf (FunClosure f al) = map ((Static ==) . fst . (!! length al) . overArgs . fst) =.< overload f al
staticFunction _ = return False
