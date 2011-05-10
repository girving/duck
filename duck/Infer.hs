{-# LANGUAGE PatternGuards, ScopedTypeVariables #-}
{-# OPTIONS -fno-warn-orphans #-}
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
  -- * Environment access
  , lookupGlobal
  , lookupDatatype
  , lookupCons
  , lookupVariances
  , lookupOver
  ) where

import Prelude hiding (lookup)
import Data.Either
import qualified Data.Map as Map
import Data.List hiding (lookup, union)
import qualified Data.List as List
import Control.Monad.State hiding (join)

import Util
import Pretty
import Var
import SrcLoc
import Type
import TypeSet
import Prims
import Lir hiding (union)
import InferMonad
import qualified Ptrie
import qualified Base

-- Some aliases for documentation purposes

type Locals = TypeEnv

-- Utility functions

-- |Insert an overload into the table.  The first argument is meant to indicate whether this is a final resolution, or a temporary one before fixpoint convergance.
insertOver :: Bool -> Var -> [TransType TypeVal] -> Overload TypeVal -> Infer ()
insertOver _final f a o = do
  --debugInfer $ "recorded" <:> prettyap f a <+> '=' <+> overRet o
  modify $ Ptrie.mapInsert f a o

-- |Lookup an overload from the table, or make one if it's partial
lookupOver :: Var -> [TypeVal] -> Infer (Maybe (Overload TypeVal))
lookupOver f tl = get >.=
  (maybe Nothing (makeover . second (fmap Ptrie.unLeaf) . Ptrie.lookup tl) . Map.lookup f)
  where
    makeover (_, Nothing) = Nothing
    makeover (tt, Just Nothing) = Just $ Over noLoc (zip tt tl) (typeClosure f tl) [] Nothing
    makeover (_, Just (Just o)) = Just o

-- |Given a set of overloads, return the transform annotations for the first @n@ arguments, if they are the same.
transOvers :: [Overload t] -> Int -> Maybe [Trans]
transOvers [] _ = Nothing
transOvers os n = unique $ map (map fst . (take n) . overArgs) os

lookupGlobal :: SrcLoc -> Var -> Infer TypeVal
lookupGlobal loc v = getProg >>= lp where
  lp prog
    | Just r <- Map.lookup v (progGlobalTypes prog) = return r -- fall back to global definitions
    | otherwise = inferError loc $ "unbound global variable" <+> quoted v

lookupDatatype :: SrcLoc -> TypeVal -> Infer [(Loc CVar, [TypeVal])]
lookupDatatype loc (TyCons d [t]) | d == datatypeType = case t of
  TyCons c tl -> return [(L noLoc (dataName c), map typeType tl)]
  TyVoid -> return [(L noLoc (V "Void"), [])]
  TyFun _ -> inferError loc $ "cannot pattern match on" <+> quoted (typeType t) <> "; matching on function types isn't implemented yet"
lookupDatatype loc (TyCons d types) = case dataInfo d of
  DataAlgebraic conses -> return $ map (second $ map $ substVoid $ Map.fromList $ zip (dataTyVars d) types) conses
  DataPrim _ -> typeError loc ("expected algebraic datatype, got" <+> quoted d)
lookupDatatype loc t = typeError loc ("expected datatype, got" <+> quoted t)

lookupFunction :: Var -> Infer [Overload TypePat]
lookupFunction f = getProg >>= \prog ->
  case Map.lookup f (progFunctions prog) of
    Just o -> return o
    _ -> inferError noLoc ("unbound function" <+> quoted f)

lookupCons :: [(Loc CVar, [t])] -> CVar -> Maybe [t]
lookupCons cases c = fmap snd (List.find ((c ==) . unLoc . fst) cases)

-- |Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Infer TypeEnv
prog = getProg >>= foldM (\g -> withGlobals g . definition) Map.empty . progDefinitions

definition :: Definition -> Infer [(Var,TypeVal)]
definition d@(Def vl e) = withFrame (V $ intercalate "," $ map (\(L _ (V s)) -> s) vl) [] l $ do
  t <- expr Map.empty l e
  tl <- case (vl,t) of
          (_, TyVoid) -> return $ map (const TyVoid) vl
          ([_],_) -> return [t]
          (_, TyCons c tl) | isDatatypeTuple c, length vl == length tl -> return tl
          ([],_) -> inferError l $ "expected (), got" <+> quoted t
          _ -> inferError l $ "expected" <+> length vl <> "-tuple, got" <+> quoted t
  return (zip (map unLoc vl) tl)
  where l = loc d

expr :: Locals -> SrcLoc -> Exp -> Infer TypeVal
expr env loc = exp where
  exp (ExpAtom a) = atom env loc a
  exp (ExpApply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    snd =.< apply loc t1 t2
  exp (ExpLet v e body) = do
    t <- exp e
    expr (Map.insert v t env) loc body
  exp (ExpCase a pl def) = do
    t <- atom env loc a
    case t of
      TyVoid -> return TyVoid
      t -> do
        conses <- lookupDatatype loc t
        let caseType (c,vl,e') = case lookupCons conses c of
              Just tl | length tl == length vl ->
                expr (insertVars env vl tl) loc e'
              Just tl | a <- length tl ->
                inferError loc $ "arity mismatch in pattern:" <+> quoted c <+> "expected" <+> a <+> "argument"<>sPlural tl 
                  <+>"but got" <+> quoted (hsep vl)
              Nothing ->
                inferError loc ("datatype" <+> quoted t <+> "has no constructor" <+> quoted c)
            defaultType Nothing = return []
            defaultType (Just e') = expr env loc e' >.= (:[])
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        joinList loc (caseResults ++ defaultResults)
  exp (ExpCons d c el) =
    cons loc d c =<< mapM exp el
  exp (ExpPrim op el) =
    Base.primType loc op =<< mapM exp el
  exp (ExpSpec e ts) =
    spec loc ts e =<< exp e
  exp (ExpLoc l e) = expr env l e

atom :: Locals -> SrcLoc -> Atom -> Infer TypeVal
atom _ _ (AtomVal t _) = return t
atom env loc (AtomLocal v) = case Map.lookup v env of
  Just r -> return r
  Nothing -> inferError loc $ "internal error: unbound local variable" <+> quoted v
atom _ loc (AtomGlobal v) = lookupGlobal loc v

cons :: SrcLoc -> Datatype -> Int -> [TypeVal] -> Infer TypeVal
cons loc d c args = do
  conses <- case dataInfo d of
    DataAlgebraic conses -> return conses
    DataPrim _ -> typeError loc ("expected algebraic datatype, got" <+> quoted d)
  let (cv,tl) = conses !! c
  tenv <- typeReError loc (quoted cv <+> "expected arguments" <+> quoted (hsep tl) <> ", got" <+> quoted (hsep args)) $
    checkLeftovers noLoc () $
    subsetList args tl
  let targs = map (\v -> Map.findWithDefault TyVoid v tenv) (dataTyVars d)
  return $ TyCons d targs

spec :: SrcLoc -> TypePat -> Exp -> TypeVal -> Infer TypeVal
spec loc ts e t = do
  tenv <- checkLeftovers loc ("type specification" <+> quoted ts <+> "is invalid") $
    typeReError loc (quoted e <+> "has type" <+> quoted t <> ", which is incompatible with type specification" <+> quoted ts) $
    subset t ts
  return $ substVoid tenv ts

join :: SrcLoc -> TypeVal -> TypeVal -> Infer TypeVal
join loc t1 t2 =
  typeReError loc ("failed to unify types" <+> quoted t1 <+> "and" <+> quoted t2) $
    union t1 t2

-- In future, we might want this to produce more informative error messages
joinList :: SrcLoc -> [TypeVal] -> Infer TypeVal
joinList loc = foldM1 (join loc)

apply :: SrcLoc -> TypeVal -> TypeVal -> Infer (Trans, TypeVal)
apply _ TyVoid _ = return (NoTrans, TyVoid)
apply loc (TyFun fl) t2 = do
  (t:tt, l) <- mapAndUnzipM fun fl
  unless (all (t ==) tt) $
    inferError loc ("conflicting transforms applying" <+> quoted fl <+> "to" <+> quoted t2)
  (,) t =.< joinList loc l
  where
  fun f@(FunArrow t a r) = do
    typeReError loc ("cannot apply" <+> quoted f <+> "to" <+> quoted t2) $
      subset'' t2 a
    return (t, r)
  fun (FunClosure f args) = do
    let atl = args ++ [t2]
    o <- maybe
      (withFrame f atl loc $ resolve f atl) -- no match, type not yet inferred
      return =<< lookupOver f atl
    return (fst $ overArgs o !! length args, overRet o)
apply loc t1 t2 = liftM ((,) NoTrans) $
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
  typeApply f = apply noLoc f

lookupVariances :: Prog -> Var -> [Variance]
lookupVariances prog c | Just d <- Map.lookup c (progDatatypes prog) = dataVariances d
lookupVariances _ _ = [] -- return [] instead of bailing so that skolemization works cleanly

overDesc :: Overload TypePat -> Doc'
overDesc o = pretty (o { overBody = Nothing }) <+> parens ("at" <+> show (overLoc o))

-- |Given a @<@ comparison function, return the elements not greater than any other
leasts :: (a -> a -> Bool) -> [a] -> [a]
leasts _ [] = []
leasts (<) (x:l)
  | any (< x) l = r
  | otherwise = x:r
  where r = leasts (<) $ filter (not . (x <)) l

-- |Resolve an overloaded application.  If all overloads are still partially applied, the result will have @overBody = Nothing@ and @overRet = typeClosure@.
resolve :: Var -> [TypeVal] -> Infer (Overload TypeVal)
resolve f args = do
  rawOverloads <- lookupFunction f -- look up possibilities
  let nargs = length args
      prune o = tryError $ subsetList args (overTypes o) >. o
      isSpecOf :: Overload TypePat -> Overload TypePat -> Bool
      isSpecOf a b = specializationList (overTypes a) (overTypes b)
      findmin = leasts isSpecOf -- prune away overloads which are more general than some other overload
      options overs = vcat $ map overDesc overs
  pruned <- mapM prune rawOverloads
  overloads <- case partitionEithers pruned of
    (errs,[]) -> typeErrors noLoc ("no matching overload for" <+> quoted f <> ", tried") $ zip (map overDesc rawOverloads) errs
    (_,os) -> return $ findmin os

  -- determine applicable argument type transform annotations
  tt <- maybe
    (inferError noLoc $ nested ("ambiguous type transforms, possibilities are:") (options overloads))
    return $ transOvers overloads nargs
  let at = zip tt args

  over <- case partition ((nargs ==) . length . overVars) overloads of
    ([o],[]) ->
      -- exactly one fully applied option: evaluate
      cache f args o
    ([],_) ->
      -- all overloads are still partially applied, so create a closure overload
      return (Over noLoc at (typeClosure f args) [] Nothing)
    _ | any ((TyVoid ==) . transType) at ->
      -- ambiguous with void arguments
      return (Over noLoc at TyVoid [] Nothing)
    _ ->
      -- ambiguous
      inferError noLoc $ nested ("ambiguous overloads for" <+> quoted f <> ", possibilities are:") (options overloads)

  insertOver True f at over
  return over

-- |Type infer a function call and cache the results
--
-- * TODO: cache currently infers every nonvoid function call at least thrice, regardless of recursion.  Fix this.
--
-- * TODO: we should tweak this so that only intermediate (non-fixpoint) types are recorded into a separate map, so that
-- they can be easily rolled back in SFINAE cases /without/ rolling back complete computations that occurred in the process.
cache :: Var -> [TypeVal] -> Overload TypePat -> Infer (Overload TypeVal)
cache f args (Over oloc atypes rt vl ~(Just e)) = do
  let (tt,types) = unzip atypes
  tenv <- checkLeftovers noLoc ("invalid overload" <+> quoted (foldr typeArrow rt types)) $
    subsetList args types
  let al = zip tt args
      tl = map (transType . fmap (substVoid tenv)) atypes
      rs = substVoid tenv rt
      or r = Over oloc (zip tt tl) r vl (Just e)
      eval = do
        r <- expr (Map.fromList (zip vl tl)) oloc e
        typeReError noLoc ("failed to unify result" <+> quoted r <+>"with return signature" <+> quoted rs) $
          union r rs
      fix final prev = do
        insertOver final f al (or prev)
        r <- eval
        if r == prev
          then return (or r)
          else if final
            then inferError noLoc "internal error: type convergence failed"
            else fix final r
  s <- get -- fork state to do speculative fixpoint
  o <- fix False TyVoid -- recursive function calls are initially assumed to be void
  put s -- restore state
  fix True (overRet o) -- and finalize with correct type

checkLeftovers :: Pretty m => SrcLoc -> m -> Infer (Either [Var] a) -> Infer a
checkLeftovers loc m f = f >>= either (\l -> 
    inferError loc (m <> "; cannot overload on contravariant variable"<>sPlural l <+> quoted (hsep l)))
  return
