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
  -- * Environment access
  , lookupDatatype
  , lookupCons
  , lookupConstructor
  , lookupVariances
  ) where

import Prelude hiding (lookup)
import Data.Maybe
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

insertOver :: Var -> [(Maybe Trans, Type)] -> Overload Type -> Infer ()
insertOver f a o = do
  --debugInfer ("recorded "++pshow f++" "++pshowlist a++" = "++pshow (overRet o))
  modify $ Ptrie.mapInsert f a o

lookupOver :: Var -> [Type] -> Infer (Maybe (Either (Maybe Trans) (Overload Type)))
lookupOver f tl = get >.=
  (fmap Ptrie.unPtrie . Ptrie.lookup tl <=< Map.lookup f)

lookupOverTrans :: Var -> [Type] -> Infer [Maybe Trans]
lookupOverTrans f tl = get >.=
  maybe [] (Ptrie.assocs tl) . Map.lookup f

transOvers :: [Overload t] -> Int -> Maybe [Maybe Trans]
transOvers [] _ = Nothing
transOvers os n = if all (tt ==) tts then Just tt else Nothing 
  where tt:tts = map (map fst . (take n) . overArgs) os

lookup :: Locals -> SrcLoc -> Var -> Infer Type
lookup env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | otherwise = getProg >>= lp where
  lp prog
    | Just r <- Map.lookup v (progGlobalTypes prog) = return r -- fall back to global definitions
    | Just _ <- Map.lookup v (progFunctions prog) = return $ typeClosure v [] -- if we find overloads, make a new closure
    | Just _ <- Map.lookup v (progDatatypes prog) = return $ typeType (TyCons v []) -- found a type constructor, return Type v
    | otherwise = inferError loc ("unbound variable " ++ qshow v)

lookupDatatype :: SrcLoc -> CVar -> [Type] -> Infer [(Loc CVar, [Type])]
lookupDatatype loc (V "Type") [t] = case t of
  TyCons c tl -> return [(Loc noLoc c, map typeType tl)]
  TyVoid -> return [(Loc noLoc (V "Void"), [])]
  TyFun _ -> inferError loc ("can't pattern match on "++qshow (typeType t)++"; matching on function types isn't implemented yet")
lookupDatatype loc tv types = getProg >>= \prog ->
  case Map.lookup tv (progDatatypes prog) of
    Just (Data _ vl cons _) -> return $ map (second $ map $ substVoid $ Map.fromList $ zip vl types) cons
    _ -> inferError loc ("unbound datatype constructor " ++ qshow tv)

lookupOverloads :: SrcLoc -> Var -> Infer [Overload TypePat]
lookupOverloads loc f = getProg >>= \prog ->
  case Map.lookup f (progFunctions prog) of
    Just o -> return o
    _ -> inferError loc ("unbound function " ++ qshow f)

lookupConstructor :: SrcLoc -> Var -> Infer (CVar, [Var], [TypePat])
lookupConstructor loc c = getProg >>= lp where
  lp prog
    | Just tc <- Map.lookup c (progConses prog)
    , Just td <- Map.lookup tc (progDatatypes prog)
    , Just tl <- lookupCons (dataConses td) c 
    = return (tc,dataTyVars td,tl)
    | otherwise = inferError loc ("unbound constructor " ++ qshow c)

lookupCons :: [(Loc CVar, [t])] -> CVar -> Maybe [t]
lookupCons cases c = fmap snd (List.find ((c ==) . unLoc . fst) cases)

-- |Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Infer TypeEnv
prog = getProg >>= foldM (\g -> withGlobals g . definition) Map.empty . progDefinitions

definition :: Definition -> Infer [(Var,Type)]
definition d@(Def vl e) = withFrame (V $ intercalate "," $ map (unV . unLoc) vl) [] l $ do
  t <- expr Map.empty l e
  tl <- case (vl,t) of
          ([_],_) -> return [t]
          (_, TyCons c tl) | isTuple c, length vl == length tl -> return tl
          _ -> inferError l ("expected "++show (length vl)++"-tuple, got "++pshow t)
  return (zip (map unLoc vl) tl)
  where l = loc d

expr :: Locals -> SrcLoc -> Exp -> Infer Type
expr env loc = exp where
  exp (Int _) = return typeInt
  exp (Chr _) = return typeChr
  exp (Var v) = lookup env loc v
  exp (Apply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    apply t1 t2 loc
  exp (Let v e body) = do
    t <- exp e
    expr (Map.insert v t env) loc body
  exp (Case _ [] Nothing) = return TyVoid
  exp (Case _ [] (Just body)) = exp body
  exp (Case v pl def) = do
    t <- lookup env loc v
    case t of
      TyVoid -> return TyVoid
      TyCons tv types -> do
        conses <- lookupDatatype loc tv types
        let caseType (c,vl,e') = case lookupCons conses c of
              Just tl | length tl == length vl -> 
                expr (foldl (\e (v,t) -> Map.insert v t e) env (zip vl tl)) loc e'
              Just tl | a <- length tl ->
                inferError loc ("arity mismatch in pattern: "++qshow c++" expected "++show a++" argument"++(if a == 1 then "" else "s")
                  ++" but got ["++intercalate ", " (map pshow vl)++"]")
              Nothing -> 
                inferError loc ("datatype "++qshow tv++" has no constructor "++qshow c)
            defaultType Nothing = return []
            defaultType (Just e') = expr env loc e' >.= (:[])
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        joinList loc (caseResults ++ defaultResults)
      _ -> typeError loc ("expected datatype, got "++qshow t)
  exp (Cons c el) =
    cons loc c =<< mapM exp el
  exp (Prim op el) =
    Base.primType loc op =<< mapM exp el
  exp (Bind v e1 e2) = do
    t1 <- runIO =<< exp e1
    t2 <- expr (Map.insert v t1 env) loc e2
    checkIO t2
  exp (Return e) =
    exp e >.= typeIO
  exp (PrimIO p el) = mapM exp el >>= Base.primIOType loc p >.= typeIO
  exp (Spec e ts) =
    spec loc ts e =<< exp e
  exp (ExpLoc l e) = expr env l e

cons :: SrcLoc -> CVar -> [Type] -> Infer Type
cons loc c args = do
  (tv,vl,tl) <- lookupConstructor loc c
  (tenv,leftovers) <- typeReError loc (qshow c++" expected arguments "++pshowlist tl++", got "++pshowlist args) $
    subsetList args tl
  when (not $ null leftovers) $ inferError loc (qshow c++" expected arguments "++pshowlist tl++", got "++pshowlist args++"; can't overload on contravariant " ++ showContravariantVars leftovers) -- typeError?
  let targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
  return $ TyCons tv targs where

spec :: SrcLoc -> TypePat -> Exp -> Type -> Infer Type
spec loc ts e t = do
  (tenv,leftovers) <- typeReError loc (qshow e++" has type "++qshow t++", which is incompatible with type specification "++qshow ts) $
    subset t ts
  when (not $ null leftovers) $ inferError loc ("type specification "++qshow ts++" is invalid; cannot overload on contravariant "++showContravariantVars leftovers) -- typeError?
  return $ substVoid tenv ts

join :: SrcLoc -> Type -> Type -> Infer Type
join loc t1 t2 =
  typeReError loc ("failed to unify types "++qshow t1++" and "++qshow t2) $
    union t1 t2

-- In future, we might want this to produce more informative error messages
joinList :: SrcLoc -> [Type] -> Infer Type
joinList loc = foldM1 (join loc)

apply :: Type -> Type -> SrcLoc -> Infer Type
apply TyVoid _ _ = return TyVoid
apply _ TyVoid _ = return TyVoid
apply (TyFun fl) t2 loc = joinList loc =<< mapM fun fl where
  fun (FunArrow a r) = do
    typeReError loc ("cannot apply "++qshow (typeArrow a r)++" to "++qshow t2) $
      subset'' t2 a
    return r
  fun (FunClosure f args) = do
    r <- lookupOver f args'
    case r of
      Nothing -> apply' f args' loc -- no match, type not yet inferred
      Just (Right t) -> return (overRet t) -- fully applied
      Just (Left _) -> return $ typeClosure f args' -- partially applied
    where args' = args ++ [t2]
apply t1 t2 loc | Just (TyCons c tl) <- isTypeType t1, Just t <- isTypeType t2 = do
  vl <- typeVariances c
  if length tl < length vl
    then return (typeType (TyCons c (tl++[t])))
    else typeError loc ("can't apply "++qshow t1++" to "++qshow t2++", "++qshow c++" is already fully applied")
apply t1 t2 loc = typeError loc ("can't apply "++qshow t1++" to "++qshow t2)

instance TypeMonad Infer where
  typeApply = applyTry
  typeVariances v = getProg >.= \p -> lookupVariances p v

applyTry :: Type -> Type -> Infer Type
applyTry f t = apply f t noLoc

lookupVariances :: Prog -> Var -> [Variance]
lookupVariances prog c | Just d <- Map.lookup c (progDatatypes prog) = dataVariances d
lookupVariances _ _ = [] -- return [] instead of bailing so that skolemization works cleanly

overDesc :: Overload TypePat -> Doc
overDesc o = pretty (o { overBody = Nothing }) <+> parens (pretty "at" <+> pretty (show (overLoc o)))

-- Resolve an overload.  A result of Nothing means all overloads are still partially applied.
resolve :: Var -> [Type] -> SrcLoc -> Infer (Either [Maybe Trans] (Overload TypePat))
resolve f args loc = do
  rawOverloads <- lookupOverloads loc f -- look up possibilities
  let prune o = tryError $ subsetList args (overTypes o) >. o
      isSpecOf :: Overload TypePat -> Overload TypePat -> Bool
      isSpecOf a b = specializationList (overTypes a) (overTypes b)
      isMinimal os o = all (\o' -> isSpecOf o o' || not (isSpecOf o' o)) os
      findmin o = filter (isMinimal o) o -- prune away overloads which are more general than some other overload
      options overs = nest 2 $ vcat $ map overDesc overs
      call = quotes $ pretty f <+> prettylist args
  pruned <- mapM prune rawOverloads
  overloads <- case partitionEithers pruned of
    (errs,[]) -> typeErrors loc (call <+> pretty "does not match any overloads, tried") $ zip (map overDesc rawOverloads) errs
    (_,os) -> return $ findmin os
  case partition ((length args ==) . length . overVars) overloads of
    ([],os) -> maybe -- all overloads are still partially applied
      (inferError loc (call <+> pretty "has conflicting type transforms with other overloads"))
      (return . Left)
      $ transOvers os (succ $ length args) -- one day the succ might be able to go away
    ([o],[]) -> return (Right o) -- exactly one fully applied option
    (fully,[]) -> inferError loc (call <+> pretty "is ambiguous, possibilities are:" $$ options fully)
    (fully,partially) -> inferError loc (call <+> pretty "is ambiguous, could either be fully applied as:" $$ options fully $$ pretty "or partially applied as:" $$ options partially)

-- |Overloaded function application
apply' :: Var -> [Type] -> SrcLoc -> Infer Type
apply' f args loc = do
  overload <- resolve f args loc
  let tt = either id (map fst . overArgs) overload
  ctt <- lookupOverTrans f args
  unless (and $ zipWith (==) tt ctt) $
    inferError loc (qshow (pretty f <+> prettylist args) ++ " has conflicting type transforms with other overloads")
  case overload of
    Left tt -> do
      let t = typeClosure f args
      insertOver f (zip tt args) (Over noLoc [] t [] Nothing)
      return t
    Right o -> cache f args o loc

-- |Type infer a function call and cache the results
--
-- * TODO: cache currently infers every nonvoid function call at least twice, regardless of recursion.  Fix this.
--
-- * TODO: we should tweak this so that only intermediate (non-fixpoint) types are recorded into a separate map, so that
-- they can be easily rolled back in SFINAE cases /without/ rolling back complete computations that occurred in the process.
cache :: Var -> [Type] -> Overload TypePat -> SrcLoc -> Infer Type
cache f args (Over oloc atypes r vl e) loc = do
  let (tt,types) = unzip atypes
      call = qshow (pretty f <+> prettylist args)
  (tenv, leftovers) <- subsetList args types
  unless (null leftovers) $ 
    inferError loc (call++" uses invalid overload "++qshow (foldr typeArrow r types)++"; can't overload on contravariant "++showContravariantVars leftovers)
  let al = zip tt args
      tl = map (argType . fmap (substVoid tenv)) atypes
      rs = substVoid tenv r
      fix prev e = do
        insertOver f al (Over oloc (zip tt tl) prev vl (Just e))
        r' <- withFrame f args loc (expr (Map.fromList (zip vl tl)) oloc e)
        r <- typeReError loc ("in call "++call++", failed to unify result "++qshow r'++" with return signature "++qshow rs) $
          union r' rs
        if r == prev
          then return prev
          else fix r e
  maybe (return TyVoid) (fix TyVoid) e -- recursive function calls are initially assumed to be void

-- |Verify that main exists and has type IO ().
main :: Infer ()
main = do
  main <- lookup Map.empty noLoc (V "main")
  typeReError noLoc ("main has type "++qshow main++", but should have type IO ()") $
    subset'' main (typeIO typeUnit)

-- |This is the analog for 'Interp.runIO' for types.  It exists by analogy even though it is very simple.
runIO :: Type -> Infer Type
runIO io | Just t <- isTypeIO io = return t
runIO t = typeError noLoc ("expected IO type, got "++qshow t)

-- |Verify that a type is in IO, and leave it unchanged if so
checkIO :: Type -> Infer Type
checkIO t = typeIO =.< runIO t
