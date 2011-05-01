{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck Ir to Lir Conversion
--
-- Processes "Ir" into its final representation for processing.
-- 'Exp' is unchanged except that 'Lambdas' have all been lifted to top-level functions.
-- Top-level declarations have been organized and mapped.

module ToLir
  ( prog
  ) where

import Prelude hiding (mapM)
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
import Pretty
import Type
import Lir
import qualified Ir
import Prims
import Memory

-- Lambda lifting: IR to Lifted IR conversion

type Globals = InScopeSet

prog :: ModuleName -> [Ir.Decl] -> Prog
prog name decls = complete $ fst $ flip execState (empty name, globals) $ do
  mapM_ decl decls
  modify $ first $ \p -> p { progDefinitions = reverse (progDefinitions p) }
  modify $ first $ \p -> p { progDatatypes = variances (progDatatypes p) }

  where

  globals = foldl decl_vars Set.empty decls

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
      invVars (TsCons c tl) = concat [if Set.member (c,i) inv then freeVars t else invVars t | (i,t) <- zip [0..] tl]
      invVars (TsFun fl) = concatMap fun fl where
        fun (FunArrow s t) = freeVars s ++ invVars t
        fun (FunClosure _ tl) = concatMap freeVars tl
      invVars TsVoid = []
    finish inv = Map.mapWithKey f datatypes where
      f c (Data tc l args cl _) = Data tc l args cl (map variance [0..arity-1]) where
        arity = length args
        variance i = if Set.member (c,i) inv then Invariant else Covariant

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
decl (Ir.Over v t e) = do
  let (tl,r,vl,e') = unwrapTypeLambda (toType t) e
  e <- expr (Set.fromList vl) noLocExpr e'
  overload v tl r vl e
decl (Ir.LetD v e) = do
  e <- expr Set.empty noLocExpr e
  definition [v] e
decl (Ir.LetM vl e) = do
  e <- expr Set.empty noLocExpr e
  definition vl e
decl (Ir.Data (L l tc) tvl cases) =
  modify $ first $ \p -> p { progDatatypes = Map.insertWith exists tc (Data tc l tvl cases' []) (progDatatypes p) }
  where exists _ o = dupError tc l (dataLoc o)
        cases' = map (\(v,t) -> (v,map toType t)) cases

-- |Convert a type
toType :: Ir.TypePat -> TypePat
toType (Ir.TsVar v) = TsVar v
toType (Ir.TsCons c tl) = TsCons c (map toType tl)
toType (Ir.TsFun fl) = TsFun $ map fun fl where
  fun (Ir.FunArrow s t) = FunArrow (toType s) (toType t)
  fun (Ir.FunClosure f tl) = FunClosure f (map toType tl)
toType Ir.TsVoid = TsVoid

-- |Add a toplevel statement
definition :: [Loc Var] -> Exp -> State (Prog, Globals) ()
definition vl e = modify $ first $ \p -> p { progDefinitions = (Def vl e) : progDefinitions p }

-- |Add a global overload
overload :: Loc Var -> [TypeSetArg] -> TypePat -> [Var] -> Exp -> State (Prog, Globals) ()
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

type TypeSetArg = TransType TypePat

-- |Extracts the annotation from a possibly annotated argument type.
typeArg :: TypePat -> TypeSetArg
typeArg (TsCons (V "Delayed") [t]) = (Delayed, t)
typeArg t = (NoTrans, t)

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
expr locals l (Ir.Spec e t) = expr locals l e >.= \e -> ExpSpec e (toType t)
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
