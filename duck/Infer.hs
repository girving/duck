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
  , cons
  , spec
  , apply
  , runIO
  , main
  , isTypeType
  -- * Environment access
  , lookup
  , lookupDatatype
  , lookupCons
  , lookupConstructor
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
import Lir hiding (prog, union)
import InferMonad
import qualified Ptrie
import qualified Base

-- Some aliases for documentation purposes

type Locals = TypeEnv

-- Utility functions

-- |Insert an overload into the table.  The first argument is meant to indicate whether this is a final resolution, or a temporary one before fixpoint convergance.
insertOver :: Bool -> Var -> [(Trans, TypeVal)] -> Overload TypeVal -> Infer ()
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
transOvers os n = if all (tt ==) tts then Just tt else Nothing
  where tt:tts = map (map fst . (take n) . overArgs) os

lookup :: Locals -> SrcLoc -> Var -> Infer TypeVal
lookup env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | otherwise = getProg >>= lp where
  lp prog
    | Just r <- Map.lookup v (progGlobalTypes prog) = return r -- fall back to global definitions
    | Just _ <- Map.lookup v (progFunctions prog) = return $ typeClosure v [] -- if we find overloads, make a new closure
    | Just _ <- Map.lookup v (progDatatypes prog) = return $ typeType (TyCons v []) -- found a type constructor, return Type v
    | otherwise = inferError loc $ "unbound variable" <+> quoted v

lookupDatatype :: SrcLoc -> TypeVal -> Infer [(Loc CVar, [TypeVal])]
lookupDatatype loc (TyCons (V "Type") [t]) = case t of
  TyCons c tl -> return [(L noLoc c, map typeType tl)]
  TyVoid -> return [(L noLoc (V "Void"), [])]
  TyFun _ -> inferError loc $ "cannot pattern match on" <+> quoted (typeType t) <> "; matching on function types isn't implemented yet"
lookupDatatype loc (TyCons tv types) = getProg >>= \prog ->
  case Map.lookup tv (progDatatypes prog) of
    Just (Data _ _ vl cons _) -> return $ map (second $ map $ substVoid $ Map.fromList $ zip vl types) cons
    _ -> inferError loc ("unbound datatype constructor" <+> quoted tv)
lookupDatatype loc t = typeError loc ("expected datatype, got" <+> quoted t)

lookupFunction :: Var -> Infer [Overload TypePat]
lookupFunction f = getProg >>= \prog ->
  case Map.lookup f (progFunctions prog) of
    Just o -> return o
    _ -> inferError noLoc ("unbound function" <+> quoted f)

lookupConstructor :: SrcLoc -> Var -> Infer (CVar, [Var], [TypePat])
lookupConstructor loc c = getProg >>= lp where
  lp prog
    | Just tc <- Map.lookup c (progConses prog)
    , Just td <- Map.lookup tc (progDatatypes prog)
    , Just tl <- lookupCons (dataConses td) c
    = return (tc,dataTyVars td,tl)
    | otherwise = inferError loc ("unbound constructor" <+> quoted c)

lookupCons :: [(Loc CVar, [t])] -> CVar -> Maybe [t]
lookupCons cases c = fmap snd (List.find ((c ==) . unLoc . fst) cases)

-- |Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Infer TypeEnv
prog = getProg >>= foldM (\g -> withGlobals g . definition) Map.empty . progDefinitions

definition :: Definition -> Infer [(Var,TypeVal)]
definition d@(Def vl e) = withFrame (V $ intercalate "," $ map (var . unLoc) vl) [] l $ do
  t <- expr Map.empty l e
  tl <- case (vl,t) of
          ([_],_) -> return [t]
          (_, TyCons c tl) | isTuple c, length vl == length tl -> return tl
          _ -> inferError l $ "expected" <+> length vl <> "-tuple, got" <+> quoted t
  return (zip (map unLoc vl) tl)
  where l = loc d

expr :: Locals -> SrcLoc -> Exp -> Infer TypeVal
expr env loc = exp where
  exp (ExpInt _) = return typeInt
  exp (ExpChar _) = return typeChar
  exp (ExpVar v) = lookup env loc v
  exp (ExpApply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    apply loc t1 t2
  exp (ExpLet v e body) = do
    t <- exp e
    expr (Map.insert v t env) loc body
  exp (ExpCase _ [] Nothing) = return TyVoid
  exp (ExpCase _ [] (Just body)) = exp body
  exp (ExpCase v pl def) = do
    t <- lookup env loc v
    case t of
      TyVoid -> return TyVoid
      t -> do
        conses <- lookupDatatype loc t
        let caseType (c,vl,e') = case lookupCons conses c of
              Just tl | length tl == length vl ->
                expr (insertList env vl tl) loc e'
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
  exp (ExpCons c el) =
    cons loc c =<< mapM exp el
  exp (ExpPrim op el) =
    Base.primType loc op =<< mapM exp el
  exp (ExpBind v e1 e2) = do
    t1 <- runIO =<< exp e1
    t2 <- expr (Map.insert v t1 env) loc e2
    checkIO t2
  exp (ExpReturn e) =
    exp e >.= typeIO
  exp (ExpSpec e ts) =
    spec loc ts e =<< exp e
  exp (ExpLoc l e) = expr env l e

cons :: SrcLoc -> CVar -> [TypeVal] -> Infer TypeVal
cons loc c args = do
  (tv,vl,tl) <- lookupConstructor loc c
  tenv <- typeReError loc (quoted c<+>"expected arguments" <+> quoted (hsep tl) <> ", got" <+> quoted (hsep args)) $
    checkLeftovers noLoc () $
    subsetList args tl
  let targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
  return $ TyCons tv targs

spec :: SrcLoc -> TypePat -> Exp -> TypeVal -> Infer TypeVal
spec loc ts e t = do
  tenv <- checkLeftovers loc ("type specification" <+> quoted ts <+> "is invalid") $
    typeReError loc (quoted e<+>"has type" <+> quoted t <> ", which is incompatible with type specification" <+> quoted ts) $
    subset t ts
  return $ substVoid tenv ts

join :: SrcLoc -> TypeVal -> TypeVal -> Infer TypeVal
join loc t1 t2 =
  typeReError loc ("failed to unify types" <+> quoted t1 <+> "and" <+> quoted t2) $
    union t1 t2

-- In future, we might want this to produce more informative error messages
joinList :: SrcLoc -> [TypeVal] -> Infer TypeVal
joinList loc = foldM1 (join loc)

apply :: SrcLoc -> TypeVal -> TypeVal -> Infer TypeVal
apply _ TyVoid _ = return TyVoid
apply loc (TyFun fl) t2 = joinList loc =<< mapM fun fl where
  fun f@(FunArrow a r) = do
    typeReError loc ("cannot apply" <+> quoted f <+> "to" <+> quoted t2) $
      subset'' t2 a
    return r
  fun (FunClosure f args) = do
    let atl = args ++ [t2]
    o <- maybe
      (withFrame f atl loc $ resolve f atl) -- no match, type not yet inferred
      return =<< lookupOver f atl
    return (overRet o)
apply loc t1 t2 = do
  r <- isTypeType t1
  case r of
    Just (TyCons c tl) -> do
      vl <- typeVariances c
      if length tl < length vl
        then typeType =.< if c == V "Type" then return t2 else do
          r <- isTypeType t2
          case r of
            Just t -> return $ TyCons c (tl++[t])
            _ -> typeError loc ("cannot apply" <+> quoted t1 <+> "to non-type" <+> quoted t2)
        else typeError loc ("cannot apply" <+> quoted t1 <+> "to" <+> quoted t2 <> "," <+> quoted c <+> "is already fully applied")
    _ -> typeError loc ("cannot apply" <+> quoted t1 <+> "to" <+> quoted t2)

isTypeC1 :: String -> TypeVal -> Infer (Maybe TypeVal)
isTypeC1 c tt = do
  r <- tryError $ subset tt (TsCons (V c) [TsVar x])
  return $ case r of
    Right (Right env) | Just t <- Map.lookup x env -> Just t
    _ -> Nothing
  where x = V "x"

isTypeType :: TypeVal -> Infer (Maybe TypeVal)
isTypeType = isTypeC1 "Type"

isTypeIO :: TypeVal -> Infer (Maybe TypeVal)
isTypeIO = isTypeC1 "IO"

instance TypeMonad Infer where
  typeApply = apply noLoc
  typeVariances v = getProg >.= \p -> lookupVariances p v

lookupVariances :: Prog -> Var -> [Variance]
lookupVariances prog c | Just d <- Map.lookup c (progDatatypes prog) = dataVariances d
lookupVariances _ _ = [] -- return [] instead of bailing so that skolemization works cleanly

overDesc :: Overload TypePat -> Doc'
overDesc o = pretty (o { overBody = Nothing }) <+> parens ("at" <+> show (overLoc o))

-- |Resolve an overloaded application.  If all overloads are still partially applied, the result will have @overBody = Nothing@ and @overRet = typeClosure@.
resolve :: Var -> [TypeVal] -> Infer (Overload TypeVal)
resolve f args = do
  rawOverloads <- lookupFunction f -- look up possibilities
  let nargs = length args
      prune o = tryError $ subsetList args (overTypes o) >. o
      isSpecOf :: Overload TypePat -> Overload TypePat -> Bool
      isSpecOf a b = specializationList (overTypes a) (overTypes b)
      isMinimal os o = all (\o' -> isSpecOf o o' || not (isSpecOf o' o)) os
      findmin o = filter (isMinimal o) o -- prune away overloads which are more general than some other overload
      options overs = vcat $ map overDesc overs
  pruned <- mapM prune rawOverloads
  overloads <- case partitionEithers pruned of
    (errs,[]) -> typeErrors noLoc ("no matching overload, tried") $ zip (map overDesc rawOverloads) errs
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
    _ | any ((TyVoid ==) . argType) at ->
      -- ambiguous with void arguments
      return (Over noLoc at TyVoid [] Nothing)
    _ ->
      -- ambiguous
      inferError noLoc $ nested ("ambiguous overloads, possibilities are:") (options overloads)

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
      tl = map (argType . fmap (substVoid tenv)) atypes
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

-- |Verify that main exists and has type IO ().
main :: Infer ()
main = do
  main <- lookup Map.empty noLoc (V "main")
  typeReError noLoc ("main has type" <+> quoted main <> ", but should have type IO ()") $
    subset'' main (typeIO typeUnit)

-- |This is the analog for 'Interp.runIO' for types.  It exists by analogy even though it is very simple.
runIO :: TypeVal -> Infer TypeVal
runIO io = do
  r <- isTypeIO io
  case r of
    Just t -> return t
    Nothing -> typeError noLoc ("expected IO type, got" <+> quoted io)

-- |Verify that a type is in IO, and leave it unchanged if so
checkIO :: TypeVal -> Infer TypeVal
checkIO t = typeIO =.< runIO t

checkLeftovers :: Pretty m => SrcLoc -> m -> Infer (Either [Var] a) -> Infer a
checkLeftovers loc m f = f >>= either (\l -> 
    inferError loc (m <> "; cannot overload on contravariant variable"<>sPlural l <+> quoted (hsep l)))
  return
