{-# LANGUAGE PatternGuards #-}
-- Duck Lifted Intermediate Representation

module Lir
  ( Prog(..)
  , Datatype, Overload, Statement
  , Exp(..), Binop(..), PrimIO(..)
  , Ir.binopString
  , prog
  , union
  ) where

import Prelude hiding (mapM)
import Var
import Type
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM)
import Data.Traversable (mapM)

import Var
import Util
import Pretty
import Text.PrettyPrint
import Data.List hiding (union)
import qualified Ir
import Ir (Binop, PrimIO)

-- Lifted IR data structures

data Prog = Prog
  { datatypes :: Map CVar Datatype
  , functions :: Map Var [Overload]
  , globals :: Set Var -- used to generate fresh variables
  , conses :: Map Var CVar -- map constructors to datatypes (type inference will make this go away)
  , statements :: [Statement] }

type Datatype = ([Var], [(CVar, [Type])])
type Overload = ([Type], Type, [Var], Exp)
type Statement = ([Var], Exp)

data Exp
  = Int Int
  | Var Var
  | Apply Exp Exp
  | Let Var Exp Exp
  | Cons CVar [Exp]
  | Case Exp [(CVar, [Var], Exp)] (Maybe (Var,Exp))
  | Binop Binop Exp Exp
    -- Monadic IO
  | Bind Var Exp Exp
  | Return Exp
  | PrimIO PrimIO [Exp]
  deriving Show

-- Lambda lifting: IR to Lifted IR conversion

emptyProg :: Prog
emptyProg = Prog Map.empty Map.empty Set.empty Map.empty []

prog :: [Ir.Decl] -> Prog
prog decls = flip execState emptyProg $ do
  modify $ \p -> p { globals = foldl decl_vars Set.empty decls }
  mapM_ decl decls
  modify $ \p -> p { statements = reverse (statements p) }
  p <- get
  mapM_ datatype (Map.toList (datatypes p))
  where
  datatype :: (CVar, Datatype) -> State Prog ()
  datatype (tc, (_, cases)) = mapM_ f cases where
    f :: (CVar, [Type]) -> State Prog ()
    f (c,tyl) = do
      modify $ \p -> p { conses = Map.insert c tc (conses p) }
      case tyl of
        [] -> statement [c] (Cons c [])
        _ -> function c vl (Cons c (map Var vl)) where
          vl = take (length tyl) standardVars

decl_vars :: Set Var -> Ir.Decl -> Set Var
decl_vars s (Ir.LetD v _) = Set.insert v s
decl_vars s (Ir.LetM vl _) = foldl (flip Set.insert) s vl
decl_vars s (Ir.Over v _ _) = Set.insert v s
decl_vars s (Ir.Data _ _ _) = s

-- Statements are added in reverse order
decl :: Ir.Decl -> State Prog ()
decl (Ir.LetD v e@(Ir.Lambda _ _)) = do
  let (vl,e') = unwrapLambda e
  e <- expr (Set.fromList vl) e'
  function v vl e
decl (Ir.Over v t e) = do
  let (tl,r,vl,e') = unwrapTypeLambda t e
  e <- expr (Set.fromList vl) e'
  overload v tl r vl e
decl (Ir.LetD v e) = do
  e <- expr Set.empty e
  statement [v] e
decl (Ir.LetM vl e) = do
  e <- expr Set.empty e
  statement vl e
decl (Ir.Data tc tvl cases) =
  modify $ \p -> p { datatypes = Map.insert tc (tvl,cases) (datatypes p) }

-- Add a toplevel statement
statement :: [Var] -> Exp -> State Prog ()
statement vl e = modify $ \p -> p { statements = (vl,e) : statements p }

-- Add a global overload
overload :: Var -> [Type] -> Type -> [Var] -> Exp -> State Prog ()
overload v tl r vl e = modify $ \p -> p { functions = Map.insertWith (++) v [(tl,r,vl,e)] (functions p) }

-- Add an unoverloaded global function
function :: Var -> [Var] -> Exp -> State Prog ()
function v vl e = overload v tl r vl e where
  (tl,r) = generalType vl

-- Unwrap a lambda as far as we can
unwrapLambda :: Ir.Exp -> ([Var], Ir.Exp)
unwrapLambda (Ir.Lambda v e) = (v:vl, e') where
  (vl, e') = unwrapLambda e
unwrapLambda e = ([], e)

generalType :: [a] -> ([Type], Type)
generalType vl = (tl,r) where
  r : tl = map TyVar (take (length vl + 1) standardVars)

-- Unwrap a type/lambda combination as far as we can
unwrapTypeLambda :: Type -> Ir.Exp -> ([Type], Type, [Var], Ir.Exp)
unwrapTypeLambda (TyFun t tl) (Ir.Lambda v e) = (t:tl', r, v:vl, e') where
  (tl', r, vl, e') = unwrapTypeLambda tl e
unwrapTypeLambda t e = ([], t, [], e)

-- Lambda lift an expression
expr :: Set Var -> Ir.Exp -> State Prog Exp
expr locals (Ir.Let v e@(Ir.Lambda _ _) rest) = do
  e <- lambda locals v e
  rest <- expr (Set.insert v locals) rest
  return $ Let v e rest
expr locals e@(Ir.Lambda _ _) = lambda locals (V "f") e
expr _ (Ir.Int i) = return $ Int i
expr _ (Ir.Var v) = return $ Var v
expr locals (Ir.Apply e1 e2) = do
  e1 <- expr locals e1
  e2 <- expr locals e2
  return $ Apply e1 e2
expr locals (Ir.Let v e rest) = do
  e <- expr locals e
  rest <- expr (Set.insert v locals) rest
  return $ Let v e rest
expr locals (Ir.Cons c el) = do
  el <- mapM (expr locals) el
  return $ Cons c el
expr locals (Ir.Case e pl def) = do
  e <- expr locals e
  pl <- mapM (\ (c,vl,e) -> expr (foldl (flip Set.insert) locals vl) e >.= \e -> (c,vl,e)) pl
  def <- mapM (\ (v,e) -> expr (Set.insert v locals) e >.= \e -> (v,e)) def
  return $ Case e pl def
expr locals (Ir.Binop op e1 e2) = do
  e1 <- expr locals e1
  e2 <- expr locals e2
  return $ Binop op e1 e2
expr locals (Ir.Bind v e rest) = do
  e <- expr locals e
  rest <- expr (Set.insert v locals) rest
  return $ Bind v e rest
expr locals (Ir.Return e) = Return =.< expr locals e
expr locals (Ir.PrimIO p el) = PrimIO p =.< mapM (expr locals) el

-- Lift a single lambda expression
lambda :: Set Var -> Var -> Ir.Exp -> State Prog Exp
lambda locals v e = do
  f <- freshenM v -- use the suggested function name
  let (vl,e') = unwrapLambda e
  e <- expr (foldl (flip Set.insert) locals vl) e'
  let vs = free locals e
  function f (vs ++ vl) e
  return $ foldl Apply (Var f) (map Var vs)

-- Generate a fresh variable
freshenM :: Var -> State Prog Var
freshenM v = do
  p <- get
  let v' = freshen (globals p) v
  put $ p { globals = Set.insert v' (globals p) }
  return v'

-- Compute the list of free variables in an expression
free :: Set Var -> Exp -> [Var]
free locals e = Set.toList (Set.intersection locals (f e)) where
  f :: Exp -> Set Var
  f (Int _) = Set.empty
  f (Var v) = Set.singleton v
  f (Apply e1 e2) = Set.union (f e1) (f e2)
  f (Let v e rest) = Set.union (f e) (Set.delete v (f rest))
  f (Cons _ el) = Set.unions (map f el)
  f (Case e pl def) = Set.unions (f e
    : maybe [] (\ (v,e) -> [Set.delete v (f e)]) def
    ++ [f e Set.\\ Set.fromList vl | (_,vl,e) <- pl])
  f (Binop _ e1 e2) = Set.union (f e1) (f e2)
  f (Bind v e rest) = Set.union (f e) (Set.delete v (f rest))
  f (Return e) = f e
  f (PrimIO _ el) = Set.unions (map f el)

-- Merge two programs into one

union :: Prog -> Prog -> Prog
union p1 p2 = Prog
  { datatypes = Map.unionWithKey conflict (datatypes p2) (datatypes p1)
  , functions = Map.unionWith (++) (functions p1) (functions p2)
  , globals = Set.union (globals p1) (globals p2)
  , conses = Map.unionWithKey conflict (conses p2) (conses p1)
  , statements = (statements p1) ++ (statements p2) }
  where
  conflict v _ _ = error ("conflicting datatype declarations for "++show (pretty v))

-- Pretty printing

instance Pretty Prog where
  pretty (Prog datatypes functions _ _ statements) = vcat $
       [pretty (Ir.Data t vl c) | (t,(vl,c)) <- Map.toList datatypes]
    ++ [function v tl r vl e | (v,o) <- Map.toList functions, (tl,r,vl,e) <- o]
    ++ map statement statements
    where
    function :: Var -> [Type] -> Type -> [Var] -> Exp -> Doc
    function v tl r vl e =
      text "over" <+> pretty (foldr TyFun r tl) $$
      text "let" <+> prettylist (v : vl) <+> equals <+> nest 2 (pretty e)
    statement (vl,e) =
      text "let" <+> hcat (intersperse (text ", ") (map pretty vl)) <+> equals <+> nest 2 (pretty e)

instance Pretty Exp where
  pretty' = pretty' . revert

revert :: Exp -> Ir.Exp
revert (Int i) = Ir.Int i
revert (Var v) = Ir.Var v
revert (Apply e1 e2) = Ir.Apply (revert e1) (revert e2)
revert (Let v e rest) = Ir.Let v (revert e) (revert rest)
revert (Cons c el) = Ir.Cons c (map revert el)
revert (Case e pl def) = Ir.Case (revert e) [(c,vl,revert e) | (c,vl,e) <- pl] (fmap (\ (v,e) -> (v,revert e)) def)
revert (Binop op e1 e2) = Ir.Binop op (revert e1) (revert e2)
revert (Bind v e rest) = Ir.Bind v (revert e) (revert rest)
revert (Return e) = Ir.Return (revert e)
revert (PrimIO p el) = Ir.PrimIO p (map revert el)
