{-# LANGUAGE PatternGuards, FlexibleInstances #-}
-- | Duck Lifted Intermediate Representation
--
-- Processes "Ir" into its final representation for processing.
-- 'Exp' is unchanged except that 'Lambdas' have all been lifted to top-level functions.
-- Top-level declarations have been organized and mapped.

module Lir
  ( Prog(..)
  , ProgMonad(..)
  , Datatype(..), Overload(..), Definition(..)
  , Overloads
  , Exp(..)
  , overTypes
  , empty
  , prog
  , union
  , check
  ) where

import Prelude hiding (mapM)
import Data.List hiding (union)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM, guard)
import Data.Traversable (mapM)

import Util
import Var
import SrcLoc
import Ptrie (Ptrie)
import qualified Ptrie
import Pretty
import Stage
import Type
import qualified Ir
import Prims

-- Lifted IR data structures

data Prog = Prog
  { progName :: ModuleName
  , progDatatypes :: Map CVar Datatype -- ^ all datatypes by type constructor
  , progFunctions :: Map Var [Overload TypePat] -- ^ original overload definitions by function name
  , progGlobals :: Set Var -- ^ all top-level symbols, used to generate fresh variables
  , progConses :: Map CVar CVar -- ^ map data constructors to datatypes (type inference will make this go away)
  , progOverloads :: Map Var Overloads -- ^ all overloads inferred to be needed, set after inference
  , progGlobalTypes :: TypeEnv -- ^ set after inference
  , progDefinitions :: [Definition] -- ^ list of top-level definitions
  }

-- |Datatype definition: @data TYPE VARs = { CVAR TYPEs ; ... }@
data Datatype = Data
  { dataLoc :: SrcLoc
  , dataTyVars :: [Var] -- ^ Type variable arguments
  , dataConses :: [(Loc CVar, [TypePat])] -- ^ Constructors
  , dataVariances :: [Variance] -- ^ Variances of 'dataTyVars'
  }
instance HasLoc Datatype where loc = dataLoc

-- |Overload definition, parameterized by either 'Type' or 'TypePat', depending on whether it is  a specific resolution, or the original definition
data Overload t = Over
  { overLoc :: SrcLoc
  , overArgs :: [TransType t] -- ^ Type of arguments with transform annotations
  , overRet :: !t -- ^ Type of return value
  , overVars :: [Var] -- ^ Names of arguments
  , overBody :: Maybe Exp -- ^ Definition of function, or 'Nothing' if not a fully applied function
  }
instance HasLoc (Overload t) where loc = overLoc

-- |The main overload table of specific overload resolutions used by the program.
-- Note that there may be many more entries than actual overload definitions, since every specific set of argument types creates a new overload.
type Overloads = Ptrie Type (Maybe Trans) (Overload Type)

type TypeSetArg = TransType TypePat

-- |Top-level variable definition: @(VARs) = EXP@
data Definition = Def
  { defVars :: [Loc Var] -- (tuple of) variables to assign
  , defBody :: Exp -- definition
  }
instance HasLoc Definition where loc = loc . defVars

-- |Expression.  Identical to 'Ir.Exp' except without 'Lambda'.
data Exp
  = ExpLoc SrcLoc !Exp
  | Int !Int
  | Chr !Char
  | Var !Var
  | Apply Exp Exp
  | Let !Var Exp Exp
  | Cons !CVar [Exp]
  | Case Var [(CVar, [Var], Exp)] (Maybe Exp)
  | Prim !Prim [Exp]
  | Spec Exp !TypePat
    -- Monadic IO
  | Bind !Var Exp Exp
  | Return Exp
  | PrimIO !PrimIO [Exp]
  deriving Show

class Monad m => ProgMonad m where
  getProg :: m Prog

-- |Type of arguments an overload expects to be passed (as opposed to expects to recieve)
overTypes :: Overload t -> [t]
overTypes = map snd . overArgs

-- Lambda lifting: IR to Lifted IR conversion

lirError :: Pretty s => SrcLoc -> s -> a
lirError l = fatal . locMsg l

dupError :: Pretty v => v -> SrcLoc -> SrcLoc -> a
dupError v n o = lirError n $ "duplicate definition of" <+> quoted v <> (", previously declared at" <?+> o)

empty :: ModuleName -> Prog
empty n = Prog n Map.empty Map.empty Set.empty Map.empty Map.empty Map.empty []

prog :: ModuleName -> [Ir.Decl] -> Prog
prog name decls = flip execState (empty name) $ do
  modify $ \p -> p { progGlobals = foldl decl_vars Set.empty decls }
  mapM_ decl decls
  modify $ \p -> p { progDefinitions = reverse (progDefinitions p) }
  modify $ \p -> p { progDatatypes = variances (progDatatypes p) }
  p <- get
  mapM_ datatype (Map.toList (progDatatypes p))

  where

  datatype :: (CVar, Datatype) -> State Prog ()
  datatype (tc, d) = mapM_ f (dataConses d) where
    f :: (Loc CVar, [TypePat]) -> State Prog ()
    f (c,tyl) = do
      modify $ \p -> p { progConses = Map.insert (unLoc c) tc (progConses p) }
      case tyl of
        [] -> definition [c] (Cons (unLoc c) [])
        _ -> function c vl (Cons (unLoc c) (map Var vl)) where
          vl = take (length tyl) standardVars

  -- Compute datatype argument variances via fixpoint iteration.  We start out
  -- assuming everything is covariant and gradually grow the set of invariant
  -- argument slots.  Argument slots are represented as pairs (c,i) where c is
  -- a datatype constructor and i is the argument position (starting at 0).
  variances :: Map CVar Datatype -> Map CVar Datatype
  variances datatypes = finish (fixpoint grow Set.empty) where
    fixpoint f x =
      if x == y then y else fixpoint f y
      where y = f x
    grow inv = Map.foldWithKey growCons inv datatypes
    growCons c datatype inv = foldl update inv (zip [0..] (dataTyVars datatype)) where
      update :: Set (CVar,Int) -> (Int,Var) -> Set (CVar,Int)
      update inv (i,v) = if Set.member v ivars then Set.insert (c,i) inv else inv
      ivars = Set.fromList (dataConses datatype >>= snd >>= invVars)
      -- The set of (currently known to be) invariant vars in a typeset
      invVars :: TypePat -> [Var]
      invVars (TsVar _) = []
      invVars (TsCons c tl) = concat [invVars t | (i,t) <- zip [0..] tl, Set.member (c,i) inv]
      invVars (TsFun fl) = concatMap fun fl where
        fun (FunArrow s t) = freeVars s ++ invVars t
        fun (FunClosure _ tl) = concatMap freeVars tl
      invVars TsVoid = []
    finish inv = Map.mapWithKey f datatypes where
      f c datatype = datatype{ dataVariances = map variance [0..arity-1] } where
        arity = length (dataTyVars datatype)
        variance i = if Set.member (c,i) inv then Invariant else Covariant

-- |A few consistency checks on Lir programs
check :: Prog -> ()
check prog = runSequence $ do
  let fs = Map.map loc (progFunctions prog)
  fds <- foldM def fs (progDefinitions prog)
  mapM_ (funs (Set.union (Map.keysSet fds) types)) $ Map.toList (progFunctions prog)
  mapM_ datatype (Map.toList $ progDatatypes prog)
  where
  types = Map.keysSet (progDatatypes prog)
  def s (Def vl body) = do
    let add s (Loc _ (V "_")) = return s
        add s (Loc l v) = do
          maybe nop (dupError v l) $ Map.lookup v s
          return $ Map.insert v l s 
    s <- foldM add s vl
    expr (Set.union (Map.keysSet s) types) body
    return s
  funs s (f,fl) = mapM_ fun fl where
    fun (Over l _ _ vl body) = do
      vs <- foldM (\s v -> do
        when (Set.member v s) $ lirError l $ qshow v++" appears more than once in argument list for "++qshow f
        return $ addVar v s) Set.empty vl
      maybe nop (expr (Set.union s vs)) body
  expr s = mapM_ (\(v,l) -> lirError l $ qshow v ++ " undefined") . free s noLoc
  datatype (_, d) = mapM_ cons (dataConses d) where
    cons (Loc l c,tl) = case Set.toList $ Set.fromList (concatMap freeVars tl) Set.\\ Set.fromList (dataTyVars d) of
      [] -> success
      [v] -> lirError l $ "variable "++qshow v++" is unbound in constructor "++qshow (TsCons c tl)
      fv -> lirError l $ "variables '"++pshowlist fv++"' are unbound in constructor "++qshow (TsCons c tl)

decl_vars :: InScopeSet -> Ir.Decl -> InScopeSet
decl_vars s (Ir.LetD (Loc _ v) _) = addVar v s
decl_vars s (Ir.LetM vl _) = foldl (flip addVar) s (map unLoc vl)
decl_vars s (Ir.Over (Loc _ v) _ _) = Set.insert v s
decl_vars s (Ir.Data _ _ _) = s

-- |Statements are added in reverse order
decl :: Ir.Decl -> State Prog ()
decl (Ir.LetD v e) | (vl@(_:_),e') <- unwrapLambda noLoc e = do
  e <- expr (Set.fromList vl) noLocExpr e'
  function v vl e
decl (Ir.Over v t e) = do
  let (tl,r,vl,e') = unwrapTypeLambda t e
  e <- expr (Set.fromList vl) noLocExpr e'
  overload v tl r vl e
decl (Ir.LetD v e) = do
  e <- expr Set.empty noLocExpr e
  definition [v] e
decl (Ir.LetM vl e) = do
  e <- expr Set.empty noLocExpr e
  definition vl e
decl (Ir.Data (Loc l tc) tvl cases) =
  modify $ \p -> p { progDatatypes = Map.insertWith exists tc (Data l tvl cases undefined) (progDatatypes p) }
  where exists _ o = dupError tc l (dataLoc o)

-- |Add a toplevel statement
definition :: [Loc Var] -> Exp -> State Prog ()
definition vl e = modify $ \p -> p { progDefinitions = (Def vl e) : progDefinitions p }

-- |Add a global overload
overload :: Loc Var -> [TypeSetArg] -> TypePat -> [Var] -> Exp -> State Prog ()
overload (Loc l v) tl r vl e | length vl == length tl = modify $ \p -> p { progFunctions = Map.insertWith (++) v [Over l tl r vl (Just e)] (progFunctions p) }
overload (Loc l v) tl _ vl _ = lirError l $ "overload arity mismatch for "++pshow v++": argument types "++pshowlist tl++", variables "++pshowlist vl

-- |Add an unoverloaded global function
function :: Loc Var -> [Var] -> Exp -> State Prog ()
function v vl e = overload v (map ((,) Nothing) tl) r vl e where
  (tl,r) = generalType vl

-- |Unwrap a lambda as far as we can
unwrapLambda :: SrcLoc -> Ir.Exp -> ([Var], Ir.Exp)
unwrapLambda l (Ir.Lambda v e) = (v:vl, e') where
  (vl, e') = unwrapLambda l e
unwrapLambda _ (Ir.ExpLoc l e) = unwrapLambda l e
unwrapLambda l e
  | hasLoc l = ([], Ir.ExpLoc l e)
  | otherwise = ([], e)

generalType :: [a] -> ([TypePat], TypePat)
generalType vl = (tl,r) where
  r : tl = map TsVar (take (length vl + 1) standardVars)

-- |Extracts the annotation from a possibly annotated argument type.
typeArg :: TypePat -> TypeSetArg
typeArg (TsCons (V "Delayed") [t]) = (Just Delayed, t)
typeArg t = (Nothing, t)

-- |Unwrap a type/lambda combination as far as we can
unwrapTypeLambda :: TypePat -> Ir.Exp -> ([TypeSetArg], TypePat, [Var], Ir.Exp)
unwrapTypeLambda a (Ir.Lambda v e) | Just (t,tl) <- isTypeArrow a =
  let (tl', r, vl, e') = unwrapTypeLambda tl e in
    (typeArg t:tl', r, v:vl, e')
unwrapTypeLambda t e = ([], t, [], e)

-- |Expr uses both location and current variable being defined
noLocExpr :: (SrcLoc, Maybe Var)
noLocExpr = (noLoc,Nothing)

-- |Lambda lift an expression
expr :: InScopeSet -> (SrcLoc, Maybe Var) -> Ir.Exp -> State Prog Exp
expr _ _ (Ir.Int i) = return $ Int i
expr _ _ (Ir.Chr c) = return $ Chr c
expr _ _ (Ir.Var v) = return $ Var v
expr locals l (Ir.Apply e1 e2) = do
  e1 <- expr locals l e1
  e2 <- expr locals l e2
  return $ Apply e1 e2
expr locals l@(loc,_) (Ir.Let v e rest) = do
  e <- expr locals (loc,Just v) e
  rest <- expr (addVar v locals) l rest
  return $ Let v e rest
expr locals l e@(Ir.Lambda _ _) = lambda locals l e
expr locals l (Ir.Cons c el) = do
  el <- mapM (expr locals l) el
  return $ Cons c el
expr locals l (Ir.Case v pl def) = do
  pl <- mapM (\ (c,vl,e) -> expr (foldl (flip addVar) locals vl) l e >.= \e -> (c,vl,e)) pl
  def <- mapM (expr locals l) def
  return $ Case v pl def
expr locals l (Ir.Prim prim el) = do
  el <- mapM (expr locals l) el
  return $ Prim prim el
expr locals l (Ir.Bind v e rest) = do
  e <- expr locals l e
  rest <- expr (addVar v locals) l rest
  return $ Bind v e rest
expr locals l (Ir.Return e) = Return =.< expr locals l e
expr locals l (Ir.PrimIO p el) = PrimIO p =.< mapM (expr locals l) el
expr locals l (Ir.Spec e t) = expr locals l e >.= \e -> Spec e t
expr locals (_,v) (Ir.ExpLoc l e) = ExpLoc l =.< expr locals (l,v) e

-- |Lift a single lambda expression
lambda :: InScopeSet -> (SrcLoc,Maybe Var) -> Ir.Exp -> State Prog Exp
lambda locals l@(loc,v) e = do
  f <- freshenM $ fromMaybe (V "f") v -- use the suggested function name
  let (vl,e') = unwrapLambda loc e
      localsPlus = foldr addVar locals vl
      localsMinus = foldr Set.delete locals vl
  e <- expr localsPlus l e'
  let vs = freeOf localsMinus e
  function (Loc loc f) (vs ++ vl) e
  return $ foldl Apply (Var f) (map Var vs)

-- |Generate a fresh variable
freshenM :: Var -> State Prog Var
freshenM v = do
  p <- get
  let (globals,v') = freshen (progGlobals p) $ moduleVar (progName p) v
  put $ p { progGlobals = globals }
  return v'

-- |Compute the list of free variables in an expression
freeOf :: InScopeSet -> Exp -> [Var]
freeOf locals e = Set.toList (Set.intersection locals (f e)) where
  f = Set.fromList . map fst . free Set.empty noLoc

free :: InScopeSet -> SrcLoc -> Exp -> [(Var,SrcLoc)]
free _ _ (Var (V "_")) = []
free s l (Var v) 
  | Set.notMember v s = [(v,l)]
  | otherwise = []
free _ _ (Int _) = []
free _ _ (Chr _) = []
free s l (Apply e1 e2) = free s l e1 ++ free s l e2
free s l (Let v e c) = free s l e ++ free (addVar v s) l c
free s l (Cons _ el) = concatMap (free s l) el
free s l (Case v al d) = 
  free s l (Var v) 
  ++ concatMap (\(_,vl,e) -> free (foldr addVar s vl) l e) al
  ++ maybe [] (free s l) d
free s l (Prim _ el) = concatMap (free s l) el
free s l (Bind v e c) = free s l e ++ free (addVar v s) l c
free s l (Return e) = free s l e
free s l (PrimIO _ el) = concatMap (free s l) el
free s l (Spec e _) = free s l e
free s _ (ExpLoc l e) = free s l e

-- |Merge two programs into one

union :: Prog -> Prog -> Prog
union p1 p2 = Prog
  { progName = ""
  , progDatatypes = Map.unionWithKey conflictLoc (progDatatypes p2) (progDatatypes p1)
  , progFunctions = Map.unionWith (++) (progFunctions p1) (progFunctions p2)
  , progGlobals = Set.union (progGlobals p1) (progGlobals p2)
  , progConses = Map.unionWithKey conflict (progConses p2) (progConses p1) -- XXX overloaded constructors?
  , progOverloads = Map.unionWithKey conflict (progOverloads p2) (progOverloads p1) -- XXX cross-module overloads?
  , progGlobalTypes = Map.unionWithKey conflict (progGlobalTypes p2) (progGlobalTypes p1)
  , progDefinitions = progDefinitions p1 ++ progDefinitions p2 }
  where
  conflictLoc v n o = dupError v (loc n) (loc o)
  conflict v _ _ = dupError v noLoc noLoc

-- Pretty printing

instance Pretty Prog where
  pretty prog = vcat $
       [pretty "-- datatypes"]
    ++ [pretty (Ir.Data (Loc l t) vl c) | (t,Data l vl c _) <- Map.toList (progDatatypes prog)]
    ++ [pretty "-- functions"]
    ++ [function v o | (v,os) <- Map.toList (progFunctions prog), o <- os]
    ++ [pretty "-- overloads"]
    ++ [pretty (progOverloads prog)]
    ++ [pretty "-- definitions"]
    ++ map definition (progDefinitions prog)
    where
    function :: Var -> Overload TypePat -> Doc
    function v o = nested (pretty v <+> pretty "::") (pretty o)
    definition (Def vl e) = nested (hcat (intersperse (pretty ", ") (map pretty vl)) <+> equals) (pretty e)

instance Pretty (Map Var Overloads) where
  pretty info = vcat [pr f tl o | (f,p) <- Map.toList info, (tl,o) <- Ptrie.toList p] where
    pr f tl o = nested (pretty f <+> pretty "::") (pretty (o{ overArgs = tl }))

instance (IsType t, Pretty t) => Pretty (Overload t) where
  pretty (Over _ a r _ Nothing) = hsep $ intersperse (pretty "->") (map (guard 2) (a ++ [(Nothing,r)]))
  pretty o@(Over _ _ _ v (Just e)) = sep [pretty (o{ overBody = Nothing }), equals <+> prettylist v <+> pretty "->" <+> pretty e]

instance Pretty Exp where
  pretty' = pretty' . revert

revert :: Exp -> Ir.Exp
revert (Int i) = Ir.Int i
revert (Chr c) = Ir.Chr c
revert (Var v) = Ir.Var v
revert (Apply e1 e2) = Ir.Apply (revert e1) (revert e2)
revert (Let v e rest) = Ir.Let v (revert e) (revert rest)
revert (Cons c el) = Ir.Cons c (map revert el)
revert (Case v pl def) = Ir.Case v [(c,vl,revert e) | (c,vl,e) <- pl] (fmap revert def)
revert (Prim prim el) = Ir.Prim prim (map revert el)
revert (Bind v e rest) = Ir.Bind v (revert e) (revert rest)
revert (Return e) = Ir.Return (revert e)
revert (PrimIO p el) = Ir.PrimIO p (map revert el)
revert (Spec e t) = Ir.Spec (revert e) t
revert (ExpLoc l e) = Ir.ExpLoc l (revert e)
