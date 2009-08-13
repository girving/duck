{-# LANGUAGE PatternGuards, ScopedTypeVariables #-}
-- | Duck type inference

module Infer
  ( prog
  , expr
  , apply
  , applyTry
  , resolve
  , lookupOver
  , lookupDatatype
  , lookupCons
  , lookupConstructor'
  ) where

import Var
import Type
import Util
import Pretty
import Lir hiding (prog)
import qualified Data.Map as Map
import Data.List hiding (lookup, intersect)
import qualified Data.List as List
import Control.Monad.Error hiding (guard, join)
import InferMonad
import qualified Ptrie
import Prelude hiding (lookup)
import qualified Prims
import Data.Maybe
import SrcLoc

---- Algorithm discussion:

-- The state of the type inference algorithm consists of
--
-- 1. A set of function type primitives (functors) representing maps from types to types.
-- 2. A map from variables to (possibly primitive) types.
-- 3. A set of in-progress type applications to compute fixed points in the case of recursion.

-- Some aliases for documentation purposes

type Locals = TypeEnv

-- Utility functions

insertOver :: Var -> [(Maybe Trans, Type)] -> Overload Type -> Infer ()
insertOver f a o = do
  --liftIO (putStrLn ("recorded "++(pshow f)++" "++show (prettylist a)++" = "++pshow (overRet o)))
  updateInfer $ Ptrie.mapInsert f a o

lookupOver :: Var -> [Type] -> Infer (Maybe (Either (Maybe Trans) (Overload Type)))
lookupOver f tl = getInfer >.=
  (fmap Ptrie.unPtrie . Ptrie.lookup tl <=< Map.lookup f)

lookupOverTrans :: Var -> [Type] -> Infer [Maybe Trans]
lookupOverTrans f tl = getInfer >.=
  maybe [] (Ptrie.assocs tl) . Map.lookup f

transOvers :: [Overload t] -> Int -> Maybe [Maybe Trans]
transOvers [] _ = Nothing
transOvers os n = if all (tt ==) tts then Just tt else Nothing 
  where tt:tts = map (map fst . (take n) . overArgs) os

lookup :: Prog -> Locals -> SrcLoc -> Var -> Infer Type
lookup prog env loc v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v (progGlobalTypes prog) = return r -- fall back to global definitions
  | Just _ <- Map.lookup v (progFunctions prog) = return $ TyClosure [(v,[])] -- if we find overloads, make a new closure
  | otherwise = typeError loc ("unbound variable " ++ show v)

lookupDatatype :: Prog -> SrcLoc -> CVar -> Infer Datatype
lookupDatatype prog loc tv
  | Just d <- Map.lookup tv (progDatatypes prog) = return d
  | otherwise = typeError loc ("unbound datatype constructor " ++ show tv)

lookupOverloads :: Prog -> SrcLoc -> Var -> Infer [Overload TypeSet]
lookupOverloads prog loc f
  | Just o <- Map.lookup f (progFunctions prog) = return o
  | otherwise = typeError loc ("unbound function " ++ show f)

lookupConstructor' :: Prog -> Var -> Maybe (CVar, [Var], [TypeSet])
lookupConstructor' prog c
  | Just tc <- Map.lookup c (progConses prog)
  , Just td <- Map.lookup tc (progDatatypes prog)
  , Just tl <- lookupCons (dataConses td) c 
  = Just (tc,dataTyVars td,tl)
  | otherwise = Nothing

lookupConstructor :: Prog -> SrcLoc -> Var -> Infer (CVar, [Var], [TypeSet])
lookupConstructor prog loc c = 
  maybe (typeError loc ("unbound constructor " ++ show c)) return $
    lookupConstructor' prog c

lookupCons :: [(Loc CVar, [TypeSet])] -> CVar -> Maybe [TypeSet]
lookupCons cases c = fmap snd (List.find ((c ==) . unLoc . fst) cases)

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: Prog -> Infer Prog
prog prog = do
  prog <- foldM definition prog (progDefinitions prog)
  info <- getInfer
  return $ prog{ progOverloads = info }

definition :: Prog -> Definition -> Infer Prog
definition prog (Def vl e) = withFrame (unLoc $ head vl) [] (srcLoc $ head vl) $ do -- XXX head
  t <- expr prog Map.empty noLoc e
  tl <- case (vl,t) of
          ([_],_) -> return [t]
          (_, TyCons c tl) | istuple c, length vl == length tl -> return tl
          _ -> typeError noLoc ("expected "++show (length vl)++"-tuple, got "++(pshow t))
  return $ prog { progGlobalTypes = foldl (\g (v,t) -> Map.insert (unLoc v) t g) (progGlobalTypes prog) (zip vl tl) }

expr :: Prog -> Locals -> SrcLoc -> Exp -> Infer Type
expr prog env loc = exp where
  exp (Int _) = return TyInt
  exp (Chr _) = return TyChr
  exp (Var v) = lookup prog env loc v
  exp (Apply e1 e2) = do
    t1 <- exp e1
    t2 <- exp e2
    apply prog t1 t2 loc
  exp (Let v e body) = do
    t <- exp e
    expr prog (Map.insert v t env) loc body
  exp (Case _ [] Nothing) = return TyVoid
  exp (Case e [] (Just (v,body))) = exp (Let v e body) -- equivalent to a let
  exp (Case e pl def) = do
    t <- exp e
    case t of
      TyVoid -> return TyVoid
      TyCons tv types -> do
        td <- lookupDatatype prog loc tv
        let tenv = Map.fromList (zip (dataTyVars td) types)
            caseType (c,vl,e')
              | Just tl <- lookupCons (dataConses td) c, a <- length tl =
                  if length vl == a then
                    let tl' = map (subst tenv) tl in
                    case mapM unsingleton tl' of
                      Nothing -> typeError loc ("datatype declaration "++(pshow tv)++" is invalid, constructor "++(pshow c)++" has nonconcrete types "++show (prettylist tl'))
                      Just tl -> expr prog (foldl (\e (v,t) -> Map.insert v t e) env (zip vl tl)) loc e'
                  else
                    typeError loc ("arity mismatch in pattern: "++(pshow c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
                      ++" but got ["++concat (intersperse ", " (map (show . pretty) vl))++"]")
              | otherwise = typeError loc ("datatype "++(pshow tv)++" has no constructor "++(pshow c))
            defaultType Nothing = return []
            defaultType (Just (v,e')) = expr prog (Map.insert v t env) loc e' >.= \t -> [t]
        caseResults <- mapM caseType pl
        defaultResults <- defaultType def
        joinList prog loc (caseResults ++ defaultResults)
      _ -> typeError loc ("expected datatype, got "++(pshow t))
  exp (Cons c el) = do
    args <- mapM exp el
    (tv,vl,tl) <- lookupConstructor prog loc c
    result <- runMaybeT $ unifyList (applyTry prog) tl args
    case result of
      Just (tenv,[]) -> return $ TyCons tv targs where
        targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
      _ -> typeError loc ((pshow c)++" expected arguments "++show (prettylist tl)++", got "++show (prettylist args))
  exp (Lir.Prim op el) =
    Prims.primType loc op =<< mapM exp el
  exp (Bind v e1 e2) = do
    t <- runIO =<< exp e1
    t <- expr prog (Map.insert v t env) loc e2
    checkIO t
  exp (Return e) = exp e >.= TyIO
  exp (PrimIO p el) = mapM exp el >>= Prims.primIOType loc p >.= TyIO
  exp (Spec e ts) = do
    t <- exp e
    result <- runMaybeT $ unify (applyTry prog) ts t
    case result of
      Just (tenv,[]) -> return $ substVoid tenv ts
      Nothing -> typeError loc ((pshow e)++" has type '"++(pshow t)++"', which is incompatible with type specification '"++(pshow ts))
      Just (_,leftovers) -> typeError loc ("type specification '"++(pshow ts)++"' is invalid; can't overload on contravariant "++showContravariantVars leftovers)
  exp (ExpLoc l e) = expr prog env l e

join :: Prog -> SrcLoc -> Type -> Type -> Infer Type
join prog loc t1 t2 = do
  result <- runMaybeT $ intersect (applyTry prog) t1 t2
  case result of
    Just t -> return t
    _ -> typeError loc ("failed to unify types "++(pshow t1)++" and "++(pshow t2))

-- In future, we might want this to produce more informative error messages
joinList :: Prog -> SrcLoc -> [Type] -> Infer Type
joinList prog loc = foldM1 (join prog loc)

apply :: Prog -> Type -> Type -> SrcLoc -> Infer Type
apply _ TyVoid _ _ = return TyVoid
apply _ _ TyVoid _ = return TyVoid
apply prog (TyClosure fl) t2 loc = joinList prog loc =<< mapM ap fl where
  ap :: (Var,[Type]) -> Infer Type
  ap (f,args) = do
    r <- lookupOver f args'
    case r of
      Nothing -> apply' prog f args' loc -- no match, type not yet inferred
      Just (Right t) -> return (overRet t) -- fully applied
      Just (Left _) -> return $ TyClosure [(f,args')] -- partially applied
    where args' = args ++ [t2]
apply prog (TyFun a r) t2 loc = do
  result <- runMaybeT $ unify'' (applyTry prog) a t2
  case result of
    Just () -> return r
    _ -> typeError loc ("cannot apply '"++(pshow (TyFun a r))++"' to '"++(pshow t2)++"'")
apply _ t1 _ loc = typeError loc ("expected a -> b, got " ++ (pshow t1))

applyTry :: Prog -> Type -> Type -> MaybeT Infer Type
applyTry prog f t = catchError (lift $ apply prog f t noLoc) (\_ -> nothing)

-- Resolve an overload.  A result of Nothing means all overloads are still partially applied.
resolve :: Prog -> Var -> [Type] -> SrcLoc -> Infer (Either [Maybe Trans] (Overload TypeSet))
resolve prog f args loc = do
  rawOverloads <- lookupOverloads prog loc f -- look up possibilities
  let call = show (pretty f <+> prettylist args)
      prune o = runMaybeT $ unifyList (applyTry prog) (overTypes o) args >. o
  overloads <- catMaybes =.< mapM prune rawOverloads -- prune those that don't match
  let isSpecOf :: Overload TypeSet -> Overload TypeSet -> Infer Bool
      isSpecOf a b = isJust =.< runMaybeT (unifyListSkolem (applyTry prog) (overTypes b) (overTypes a))
      isMinimal o = allM (\o' -> do
        less <- isSpecOf o o'
        more <- isSpecOf o' o
        return $ less || not more) overloads
      options overs = concatMap (\ o -> "\n  "++(pshow (foldr TsFun (overRet o) (overTypes o)))) overs
  filtered <- filterM isMinimal overloads -- prune away overloads which are more general than some other overload
  case filtered of
    [] -> typeError loc (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition ((length args ==) . length . overVars) os of
      ([],os) -> maybe -- all overloads are still partially applied
        (typeError loc (call ++ " has conflicting type transforms with other overloads"))
        (return . Left)
        $ transOvers os (succ $ length args) -- one day the succ might be able to go away
      ([o],[]) -> return (Right o) -- exactly one fully applied option
      (fully,[]) -> typeError loc (call++" is ambiguous, possibilities are"++options fully)
      (fully,partially) -> typeError loc (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)

-- Overloaded function application
apply' :: Prog -> Var -> [Type] -> SrcLoc -> Infer Type
apply' prog f args loc = do
  overload <- resolve prog f args loc
  let tt = either id (map fst . overArgs) overload
  ctt <- lookupOverTrans f args
  unless (and $ zipWith (==) tt ctt) $
    typeError loc (show (pretty f <+> prettylist args) ++ " has conflicting type transforms with other overloads")
  case overload of
    Left tt -> do
      let t = TyClosure [(f,args)]
      insertOver f (zip tt args) (Over [] t [] Nothing)
      return t
    Right o -> cache prog f args o loc

-- Type infer a function call and cache the results
-- The overload is assumed to match, since this is handled by apply.
--
-- TODO: cache currently infers every nonvoid function call at least twice, regardless of recursion.  Fix this.
-- TODO: we should tweak this so that only intermediate (non-fixpoint) types are recorded into a separate map, so that
-- they can be easily rolled back in SFINAE cases _without_ rolling back complete computations that occurred in the process.
cache :: Prog -> Var -> [Type] -> Overload TypeSet -> SrcLoc -> Infer Type
cache prog f args (Over atypes r vl e) loc = do
  let (tt,types) = unzip atypes
  Just (tenv, leftovers) <- runMaybeT $ unifyList (applyTry prog) types args
  let call = show (pretty f <+> prettylist args)
  unless (null leftovers) $ 
    typeError loc (call++" uses invalid overload "++(pshow (foldr TsFun r types))++"; can't overload on contravariant "++showContravariantVars leftovers)
  let al = zip tt args
      tl = map (argType . fmap (substVoid tenv)) atypes
      rs = substVoid tenv r
      fix prev e = do
        insertOver f al (Over (zip tt tl) prev vl (Just e))
        r' <- withFrame f args loc (expr prog (Map.fromList (zip vl tl)) loc e)
        result <- runMaybeT $ intersect (applyTry prog) r' rs
        case result of
          Nothing -> typeError loc ("in call "++call++", failed to unify result "++(pshow r')++" with return signature "++(pshow rs))
          Just r 
            | r == prev -> return prev
            | otherwise -> fix r e
  maybe (return TyVoid) (fix TyVoid) e -- recursive function calls are initially assumed to be void

-- This is the analog for Interp.runIO for types.  It exists by analogy even though it is very simple.
runIO :: Type -> Infer Type
runIO (TyIO t) = return t
runIO t = typeError noLoc ("expected IO type, got "++(pshow t))

-- Verify that a type is in IO, and leave it unchanged if so
checkIO :: Type -> Infer Type
checkIO t = TyIO =.< runIO t
