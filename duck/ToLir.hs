{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck Ir to Lir Conversion
--
-- Processes "Ir" into its final representation for processing.
-- 'Exp' is unchanged except that 'Lambdas' have all been lifted to top-level functions.
-- Top-level declarations have been organized and mapped.

module ToLir
  ( progs
  , prog
  ) where

import Prelude hiding (mapM)
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM, guard)
import Data.Traversable (mapM)
import System.IO.Unsafe

import Util
import Var
import SrcLoc
import Pretty
import Type hiding (freeVars)
import PreType
import Lir
import qualified Lir
import qualified Ir
import Prims
import Memory

-- Lambda lifting: IR to Lifted IR conversion

type Globals = InScopeSet

progs :: Prog -> [(ModuleName, [Ir.Decl])] -> Prog
progs base progs = foldl' (\p (name,decls) -> prog p name decls) base progs

prog :: Prog -> ModuleName -> [Ir.Decl] -> Prog
prog base name decls = complete denv . unreverse . fst $ flip execState start (mapM_ decl decls) where
  denv = unsafePerformIO $ datatypes (progDatatypes base) decls
  denv' = Map.unionWith (error "unexpected duplicate datatype in ToLir.prog") (progDatatypes base) denv
  globals = foldl decl_vars (Lir.globals base) decls
  start = (base { progName = name, progDatatypes = denv', progDefinitions = reverse (progDefinitions base) }, globals)
  unreverse p = p { progDefinitions = reverse (progDefinitions p) } -- Definitions are added in reverse, so reverse again

datatypes :: Map CVar Datatype -> [Ir.Decl] -> IO (Map CVar Datatype)
datatypes baseDenv decls = do
  datatypes <- alloc
  fill datatypes
  variances datatypes
  freeze datatypes

  where

  -- Extract datatype information
  info :: Map CVar (SrcLoc, [Var], [(Loc CVar, [Ir.TypePat])])
  info = foldl' decl Map.empty decls where
    decl denv (Ir.Data (L l tc) tvl cases) = case Map.lookup tc baseDenv of
      Nothing -> Map.insertWith exists tc (l,tvl,cases) denv
        where exists _ (l',_,_) = dupError tc l l'
      Just d -> dupError tc l (dataLoc d)
    decl denv _ = denv

  -- Generate uninitialized mutable precursor datatypes
  uninitialized = PreData (V "") noLoc [] [] []
  alloc :: IO (Map CVar (Ref PreDatatype))
  alloc = mapM (const $ newRef uninitialized) info

  -- Fill in datatype info
  fill :: Map CVar (Ref PreDatatype) -> IO ()
  fill datatypes = mapM_ f $ Map.toList datatypes where
    f (c,d) = writeRef d initialized where
      Just (l,args,conses) = Map.lookup c info
      initialized = PreData c l args conses' vars
      conses' = map (second $ map $ toPreType l baseDenv datatypes) conses
      vars = replicate (length args) Covariant

  -- Compute datatype argument variances via fixpoint iteration.  We start out
  -- assuming everything is covariant (see fill above) and gradually grow the set of
  -- invariant argument slots.
  variances :: Map CVar (Ref PreDatatype) -> IO ()
  variances datatypes = fixpoint grow where
    fixpoint f = do
      changed <- f
      if changed then fixpoint f else return ()
    grow :: IO Bool
    grow = or =.< mapM growCons (Map.elems datatypes)
    growCons datatype = do
      PreData c l args conses vars <- readRef datatype
      inv <- Set.fromList . concat =.< (mapM invVars $ snd =<< conses)
      let vars' = map (\v -> if Set.member v inv then Invariant else Covariant) args
      if vars /= vars' then do
        writeRef datatype (PreData c l args conses vars') 
        return True
       else return False
      where
      -- The set of (currently known to be) invariant vars in a typeset
      invVars :: PreTypePat -> IO [Var]
      invVars (TpVar _) = return []
      invVars (TpCons c tl) = do
        PreData _ _ _ _ vars <- readVol c
        concat =.< zipWithM f vars tl
        where
        f Covariant = invVars
        f Invariant = return . freeVars
      invVars (TpFun fl) = concat =.< mapM fun fl where
        fun (FunArrow s t) = (++) (freeVars s) =.< invVars t
        fun (FunClosure _ tl) = return $ concatMap freeVars tl
      invVars TpVoid = return []

  -- Freeze the mutable PreDatatypes into Datatypes
  freeze :: Map CVar (Ref PreDatatype) -> IO (Map CVar Datatype)
  freeze mutable = mapM (unsafeFreeze <=< unsafeCastRef) mutable

decl_vars :: InScopeSet -> Ir.Decl -> InScopeSet
decl_vars s (Ir.LetD (L _ v) _) = addVar v s
decl_vars s (Ir.LetM vl _) = foldl (flip addVar) s (map unLoc vl)
decl_vars s (Ir.Over (L _ v) _ _) = Set.insert v s
decl_vars s (Ir.Data _ _ _) = s

-- |Statements are added in reverse order
decl :: Ir.Decl -> State (Prog, Globals) ()
decl (Ir.LetD v e) | (vl@(_:_),e') <- unwrapLambda noLoc e = do
  e <- expr (Set.fromList vl) noLocExpr e'
  function v vl e
decl (Ir.Over v@(L l _) t e) = do
  denv <- get >.= progDatatypes . fst
  let (tl,r,vl,e') = unwrapTypeLambda t e
      tl' = map (second $ toType l denv) tl
      r' = toType l denv r
  e <- expr (Set.fromList vl) noLocExpr e'
  overload v tl' r' vl e
decl (Ir.LetD v e) = do
  e <- expr Set.empty noLocExpr e
  definition [v] e
decl (Ir.LetM vl e) = do
  e <- expr Set.empty noLocExpr e
  definition vl e
decl _ = return () -- Datatypes already processed

-- |Convert a type
toType :: SrcLoc -> Map CVar Datatype -> Ir.TypePat -> TypePat
toType _ _ (Ir.TsVar v) = TsVar v
toType l denv (Ir.TsCons c tl) = TsCons d (map (toType l denv) tl) where
  d = fromMaybe (lirError l $ "unbound datatype" <+> quoted c) (Map.lookup c denv)
toType l denv (Ir.TsFun fl) = TsFun $ map fun fl where
  fun (Ir.FunArrow s t) = FunArrow (toType l denv s) (toType l denv t)
  fun (Ir.FunClosure f tl) = FunClosure f (map (toType l denv) tl)
toType _ _ Ir.TsVoid = TsVoid

-- |Convert a pretype
toPreType :: SrcLoc -> Map CVar Datatype -> Map CVar (Ref PreDatatype) -> Ir.TypePat -> PreTypePat
toPreType _ _ _ (Ir.TsVar v) = TpVar v
toPreType l baseDenv denv (Ir.TsCons c tl) = TpCons d (map (toPreType l baseDenv denv) tl) where
  d = case c of
    _ | Just d <- Map.lookup c denv -> toVol d
    _ | Just d <- Map.lookup c baseDenv -> toVol $ unsafeCastBox d
    _ -> lirError l $ "unbound datatype" <+> quoted c
toPreType l baseDenv denv (Ir.TsFun fl) = TpFun $ map fun fl where
  fun (Ir.FunArrow s t) = FunArrow (toPreType l baseDenv denv s) (toPreType l baseDenv denv t)
  fun (Ir.FunClosure f tl) = FunClosure f (map (toPreType l baseDenv denv) tl)
toPreType _ _ _ Ir.TsVoid = TpVoid

-- |Add a toplevel statement
definition :: [Loc Var] -> Exp -> State (Prog, Globals) ()
definition vl e = modify $ first $ \p -> p { progDefinitions = (Def vl e) : progDefinitions p }

-- |Add a global overload
overload :: Loc Var -> [TransType TypePat] -> TypePat -> [Var] -> Exp -> State (Prog, Globals) ()
overload (L l v) tl r vl e | length vl == length tl = modify $ first $ \p -> p { progFunctions = Map.insertWith (++) v [Over l tl r vl (Just e)] (progFunctions p) }
overload (L l v) tl _ vl _ = lirError l $ "overload arity mismatch for" <+> quoted v <:> "argument types" <+> quoted (hsep tl) <> ", variables" <+> quoted (hsep vl)

-- |Add an unoverloaded global function
function :: Loc Var -> [Var] -> Exp -> State (Prog, Globals) ()
function v vl e = overload v (map ((,) NoTrans) tl) r vl e where
  (tl,r) = generalType vl

-- |Unwrap a lambda as far as we can
unwrapLambda :: SrcLoc -> Ir.Exp -> ([Var], Ir.Exp)
unwrapLambda l (Ir.Lambda v e) = (v:vl, e') where
  (vl, e') = unwrapLambda l e
unwrapLambda _ (Ir.ExpLoc l e) = unwrapLambda l e
unwrapLambda l e
  | hasLoc l = ([], Ir.ExpLoc l e)
  | otherwise = ([], e)

-- |Extracts the annotation from a possibly annotated argument type.
typeArg :: Ir.TypePat -> TransType Ir.TypePat
typeArg (Ir.TsCons (V "Delayed") [t]) = (Delayed, t)
typeArg t = (NoTrans, t)

-- |Unwrap a type/lambda combination as far as we can
unwrapTypeLambda :: Ir.TypePat -> Ir.Exp -> ([TransType Ir.TypePat], Ir.TypePat, [Var], Ir.Exp)
unwrapTypeLambda (Ir.TsFun [Ir.FunArrow t tl]) (Ir.Lambda v e) =
  let (tl', r, vl, e') = unwrapTypeLambda tl e in
    (typeArg t:tl', r, v:vl, e')
unwrapTypeLambda t e = ([], t, [], e)

-- |Expr uses both location and current variable being defined
noLocExpr :: (SrcLoc, Maybe Var)
noLocExpr = (noLoc,Nothing)

-- |Lambda lift an expression
expr :: InScopeSet -> (SrcLoc, Maybe Var) -> Ir.Exp -> State (Prog, Globals) Exp
expr _ _ (Ir.Int i) = return $ ExpVal typeInt $ value i
expr _ _ (Ir.Char c) = return $ ExpVal typeChar $ value c
expr _ _ (Ir.Var v) = return $ ExpVar v
expr locals l (Ir.Apply e1 e2) = do
  e1 <- expr locals l e1
  e2 <- expr locals l e2
  return $ ExpApply e1 e2
expr locals l@(loc,_) (Ir.Let v e rest) = do
  e <- expr locals (loc,Just v) e
  rest <- expr (addVar v locals) l rest
  return $ ExpLet v e rest
expr locals l e@(Ir.Lambda _ _) = lambda locals l e
expr locals l (Ir.Cons c el) = do
  el <- mapM (expr locals l) el
  return $ ExpCons c el
expr locals l (Ir.Case v pl def) = do
  pl <- mapM (\ (c,vl,e) -> expr (foldl (flip addVar) locals vl) l e >.= \e -> (c,vl,e)) pl
  def <- mapM (expr locals l) def
  return $ ExpCase v pl def
expr locals l (Ir.Prim prim el) = do
  el <- mapM (expr locals l) el
  return $ ExpPrim prim el
expr locals l (Ir.Bind v e rest) = do
  e <- expr locals l e
  rest <- expr (addVar v locals) l rest
  return $ ExpBind v e rest
expr locals l (Ir.Return e) = ExpReturn =.< expr locals l e
expr locals l@(loc,_) (Ir.Spec e t) = do
  e' <- expr locals l e
  denv <- get >.= progDatatypes . fst
  return $ ExpSpec e' (toType loc denv t)
expr locals (_,v) (Ir.ExpLoc l e) = ExpLoc l =.< expr locals (l,v) e

-- |Lift a single lambda expression
lambda :: InScopeSet -> (SrcLoc,Maybe Var) -> Ir.Exp -> State (Prog, Globals) Exp
lambda locals l@(loc,v) e = do
  f <- freshenM $ fromMaybe (V "f") v -- use the suggested function name
  let (vl,e') = unwrapLambda loc e
      localsPlus = foldr addVar locals vl
      localsMinus = foldr Set.delete locals vl
  e <- expr localsPlus l e'
  let vs = freeOf localsMinus e
  function (L loc f) (vs ++ vl) e
  return $ foldl ExpApply (ExpVar f) (map ExpVar vs)

-- |Generate a fresh variable
freshenM :: Var -> State (Prog, Globals) Var
freshenM v = do
  (p,globals) <- get
  let (globals',v') = freshen globals $ moduleVar (progName p) v
  put $ (p,globals')
  return v'
