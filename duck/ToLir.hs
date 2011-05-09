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
import qualified Ir
import Prims
import Memory
import Value

-- Lambda lifting: IR to Lifted IR conversion

progs :: Prog -> [(ModuleName, [Ir.Decl])] -> Prog
progs base progs = foldl' (\p (name,decls) -> prog p name decls) base progs

prog :: Prog -> ModuleName -> [Ir.Decl] -> Prog
prog base name decls = complete denv . unreverse . fst $ flip execState start (mapM_ decl decls) where
  denv = unsafePerformIO $ datatypes (progDatatypes base) decls
  denv' = Map.unionWith (error "unexpected duplicate datatype in ToLir.prog") (progDatatypes base) denv
  globals = foldl declVars (Lir.globals base) decls
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
  uninitialized = PreData (V "") noLoc [] [] $ PreDataPrim (-1)
  alloc :: IO (Map CVar (Ref PreDatatype))
  alloc = mapM (const $ newRef uninitialized) info

  -- Fill in datatype info
  fill :: Map CVar (Ref PreDatatype) -> IO ()
  fill datatypes = mapM_ f $ Map.toList datatypes where
    f (c,d) = writeRef d initialized where
      Just (l,args,conses) = Map.lookup c info
      initialized = PreData c l args vars $ PreDataAlgebraic conses'
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
      PreData c l args vars info <- readRef datatype
      case info of
        PreDataPrim _ -> error ("unexpected primitive datatype "++show (quoted c)++" seen in ToLir.variances")
        PreDataAlgebraic conses -> do
          inv <- Set.fromList . concat =.< (mapM invVars $ snd =<< conses)
          let vars' = map (\v -> if Set.member v inv then Invariant else Covariant) args
          if vars /= vars' then do
            writeRef datatype (PreData c l args vars' $ PreDataAlgebraic conses) 
            return True
           else return False
      where
      -- The set of (currently known to be) invariant vars in a typeset
      invVars :: PreTypePat -> IO [Var]
      invVars (TpVar _) = return []
      invVars (TpCons c tl) = do
        PreData _ _ _ vars _ <- readVol c
        concat =.< zipWithM f vars tl
        where
        f Covariant = invVars
        f Invariant = return . freeVars
      invVars (TpFun fl) = concat =.< mapM fun fl where
        fun (FunArrow _ s t) = (++) (freeVars s) =.< invVars t
        fun (FunClosure _ tl) = return $ concatMap freeVars tl
      invVars TpVoid = return []

  -- Freeze the mutable PreDatatypes into Datatypes
  freeze :: Map CVar (Ref PreDatatype) -> IO (Map CVar Datatype)
  freeze mutable = mapM (unsafeFreeze <=< unsafeCastRef) mutable

declVars :: Globals -> Ir.Decl -> Globals
declVars g (Ir.LetD (L _ v) e) | ((_:_),_) <- unwrapLambda noLoc e = insertVarWithKey kindConflict v FunctionKind g
declVars g (Ir.LetD (L _ v) _) = insertVarWithKey kindConflict v GlobalKind g
declVars g (Ir.ExpD _) = g
declVars g (Ir.LetM vl _) = foldl' (\g v -> insertVarWithKey kindConflict v GlobalKind g) g (map unLoc vl)
declVars g (Ir.Over (L _ v) _ _) = Map.insertWithKey kindConflict v FunctionKind g
declVars g (Ir.Data (L _ v) _ conses) = Map.insertWithKey kindConflict v DatatypeKind (foldl' cons g conses) where
  cons g (L _ v, tl) = Map.insertWithKey kindConflict v (case tl of [] -> GlobalKind ; _ -> FunctionKind) g

-- |Statements are added in reverse order
decl :: Ir.Decl -> State (Prog, Globals) ()
decl (Ir.LetD v e) | (vl@(_:_),e') <- unwrapLambda noLoc e = case v of
  L _ (V "_") -> return ()
  _ -> do
    e <- expr (Set.fromList (map snd vl)) noLocExpr e'
    function v vl e
decl (Ir.Over v@(L l _) t e) = do
  denv <- get >.= progDatatypes . fst
  let (tl,r,vl,e') = unwrapTypeLambda l t e
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
decl (Ir.ExpD e) = do
  e <- expr Set.empty noLocExpr e
  definition [] e
decl (Ir.Data _ _ _) = return () -- Datatypes already processed

-- |Convert a type
toType :: SrcLoc -> Map CVar Datatype -> Ir.TypePat -> TypePat
toType _ _ (Ir.TsVar v) = TsVar v
toType l denv (Ir.TsCons c tl) = TsCons d (map (toType l denv) tl) where
  d = fromMaybe (lirError l $ "unbound datatype" <+> quoted c) (Map.lookup c denv)
toType l denv (Ir.TsFun fl) = TsFun $ map fun fl where
  fun (Ir.FunArrow s t) = FunArrow tr (toType l denv s') (toType l denv t) where (tr, s') = typeArg l s
  fun (Ir.FunClosure f tl) = FunClosure f (map (toType l denv) tl)
toType l _ (Ir.TsTrans v _) = lirError l $ "cannot apply" <+> quoted v <+> "in type"
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
  fun (Ir.FunArrow s t) = FunArrow tr (toPreType l baseDenv denv s') (toPreType l baseDenv denv t) where (tr, s') = typeArg l s
  fun (Ir.FunClosure f tl) = FunClosure f (map (toPreType l baseDenv denv) tl)
toPreType l _ _ (Ir.TsTrans v _) = lirError l $ "cannot apply" <+> quoted v <+> "in type"
toPreType _ _ _ Ir.TsVoid = TpVoid

-- |Add a toplevel statement
definition :: [Loc Var] -> Exp -> State (Prog, Globals) ()
definition vl e = modify $ first $ \p -> p { progDefinitions = (Def vl e) : progDefinitions p }

-- |Add a global overload
overload :: Loc Var -> [TransType TypePat] -> TypePat -> [Var] -> Exp -> State (Prog, Globals) ()
overload (L l v) tl r vl e | length vl == length tl = modify $ first $ \p -> p 
  { progFunctions = Map.insertWith (++) v [Over l tl r vl (Just e)] (progFunctions p) }
overload (L l v) tl _ vl _ = lirError l $ "overload arity mismatch for" <+> quoted v <:> "argument types" <+> quoted (hsep tl) <> ", variables" <+> quoted (hsep vl)

-- |Add an unoverloaded global function
function :: Loc Var -> [TransType Var] -> Exp -> State (Prog, Globals) ()
function v tvl e = overload v (zip tr tl) r vl e where
  (tr,vl) = unzip tvl
  (tl,r) = generalType vl

-- |Unwrap a lambda as far as we can
unwrapLambda :: SrcLoc -> Ir.Exp -> ([TransType Var], Ir.Exp)
unwrapLambda l (Ir.Lambda tr v e) = ((maybe NoTrans (trans l) tr, v):vl, e') where
  (vl, e') = unwrapLambda l e
unwrapLambda _ (Ir.ExpLoc l e) = unwrapLambda l e
unwrapLambda l e
  | hasLoc l = ([], Ir.ExpLoc l e)
  | otherwise = ([], e)

trans :: SrcLoc -> Var -> Trans
trans _ (V "delay") = Delay
trans l v = lirError l $ "unknown transform" <+> quoted v <+> "applied"

-- |Extracts the annotation from a possibly annotated argument type.
typeArg :: SrcLoc -> Ir.TypePat -> TransType Ir.TypePat
typeArg loc (Ir.TsTrans trv t) = (trans loc trv, t)
typeArg _ t = (NoTrans, t)

-- |Unwrap a type/lambda combination as far as we can
unwrapTypeLambda :: SrcLoc -> Ir.TypePat -> Ir.Exp -> ([TransType Ir.TypePat], Ir.TypePat, [Var], Ir.Exp)
unwrapTypeLambda loc (Ir.TsFun [Ir.FunArrow t tl]) (Ir.Lambda vtr v e) = ((tr,t'):tl', r, v:vl, e') where
  (ttr, t') = typeArg loc t
  -- type transform takes precedence, but definition must match if specified
  tr = case vtr of
    Just vtr | trans loc vtr /= ttr -> lirError loc "transform applied in definition does not match type"
    _ -> ttr
  (tl', r, vl, e') = unwrapTypeLambda loc tl e
unwrapTypeLambda _ t e = ([], t, [], e)

-- |Expr uses both location and current variable being defined
noLocExpr :: (SrcLoc, Maybe Var)
noLocExpr = (noLoc,Nothing)

-- |Lambda lift an expression
expr :: InScopeSet -> (SrcLoc, Maybe Var) -> Ir.Exp -> State (Prog, Globals) Exp
expr _ _ (Ir.Int i) = return $ expVal typeInt $ value i
expr _ _ (Ir.Char c) = return $ expVal typeChar $ value c
expr locals l (Ir.Var v) = ExpAtom =.< var locals l v
expr locals l (Ir.Apply e1 e2) = do
  e1 <- expr locals l e1
  e2 <- expr locals l e2
  return $ ExpApply e1 e2
expr locals l@(loc,_) (Ir.Let v e rest) = do
  e <- expr locals (loc,Just v) e
  rest <- expr (addVar v locals) l rest
  return $ ExpLet v e rest
expr locals l e@(Ir.Lambda _ _ _) = lambda locals l e
expr locals l (Ir.Case v pl def) = do
  pl <- mapM (\ (c,vl,e) -> expr (foldl' (flip addVar) locals vl) l e >.= \e -> (c,vl,e)) pl
  def <- mapM (expr locals l) def
  a <- var locals l v
  return $ ExpCase a pl def
expr locals l (Ir.Prim prim el) = do
  el <- mapM (expr locals l) el
  return $ ExpPrim prim el
expr locals l@(loc,_) (Ir.Spec e t) = do
  e' <- expr locals l e
  denv <- get >.= progDatatypes . fst
  return $ ExpSpec e' (toType loc denv t)
expr locals (_,v) (Ir.ExpLoc l e) = ExpLoc l =.< expr locals (l,v) e

var :: InScopeSet -> (SrcLoc, Maybe Var) -> Var -> State (Prog, Globals) Atom
var locals _ v | Set.member v locals = return $ AtomLocal v
var _ (loc,_) v = do
  (prog, globals) <- get
  case Map.lookup v globals of
    Just GlobalKind -> return $ AtomGlobal v
    Just DatatypeKind | Just d <- Map.lookup v (progDatatypes prog) -> return $ AtomVal (typeType (TyCons d [])) valEmpty
    Just VoidKind -> return $ AtomVal (typeType TyVoid) valEmpty
    Just DatatypeKind -> lirError loc $ "internal error: unexpected unbound datatype" <+> quoted v
    Just FunctionKind -> return $ closure v
    Nothing -> lirError loc $ "unbound variable" <+> quoted v

closure :: Var -> Atom
closure v = AtomVal (typeClosure v []) (value $ ValClosure v [] [])

-- |Lift a single lambda expression
lambda :: InScopeSet -> (SrcLoc,Maybe Var) -> Ir.Exp -> State (Prog, Globals) Exp
lambda locals l@(loc,v) e = do
  f <- freshenM $ fromMaybe (V "f") v -- use the suggested function name
  let (vl,e') = unwrapLambda loc e
      vls = Set.fromList $ filter (/= V "_") (map snd vl)
      localsPlus = Set.union locals vls
  e <- expr localsPlus l e'
  let vs = free vls e
  function (L loc f) (map ((,) NoTrans) vs ++ vl) e
  return $ foldl ExpApply (ExpAtom $ closure f) (map expLocal vs)

-- |Generate a fresh variable
freshenM :: Var -> State (Prog, Globals) Var
freshenM v = do
  (p,globals) <- get
  let (globals',v') = freshenKind globals (moduleVar (progName p) v) FunctionKind
  put $ (p,globals')
  return v'
