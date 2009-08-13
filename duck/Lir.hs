{-# LANGUAGE PatternGuards, FlexibleInstances #-}
-- | Duck Lifted Intermediate Representation

module Lir
  ( Prog(..)
  , Datatype(..), Overload(..), Definition(..)
  , Overloads
  , Exp(..), Binop(..), Prim(..), PrimIO(..)
  , overTypes
  , Ir.binopString
  , prog
  , union
  ) where

import Prelude hiding (mapM)
import Type
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM, guard)
import Data.Traversable (mapM)

import Var
import Util
import SrcLoc
import Ptrie (Ptrie)
import qualified Ptrie
import Pretty
import Data.List hiding (union)
import qualified Ir
import Ir (Prim, Binop, PrimIO)

-- Lifted IR data structures

data Prog = Prog
  { progDatatypes :: Map CVar Datatype
  , progFunctions :: Map Var [Overload TypeSet]
  , progGlobals :: Set Var -- used to generate fresh variables
  , progConses :: Map Var CVar -- map constructors to datatypes (type inference will make this go away)
  , progOverloads :: Map Var Overloads -- set after inference
  , progGlobalTypes :: TypeEnv -- set after inference
  , progDefinitions :: [Definition] }

data Datatype = Data
  { dataLoc :: SrcLoc
  , dataTyVars :: [Var]
  , dataConses :: [(Loc CVar, [TypeSet])]
  }

data Overload t = Over
  { overArgs :: [TransType t]
  , overRet :: t
  , overVars :: [Var]
  , overBody :: Maybe Exp
  }

type Overloads = Ptrie Type (Maybe Trans) (Overload Type)

data Definition = Def
  { defVars :: [Loc Var]
  , defBody :: Exp
  }

data Exp
  = ExpLoc SrcLoc Exp
  | Int Int
  | Chr Char
  | Var Var
  | Apply Exp Exp
  | Let Var Exp Exp
  | Cons CVar [Exp]
  | Case Exp [(CVar, [Var], Exp)] (Maybe (Var,Exp))
  | Spec Exp TypeSet
  | Prim Prim [Exp]
    -- Monadic IO
  | Bind Var Exp Exp
  | Return Exp
  | PrimIO PrimIO [Exp]
  deriving Show

overTypes :: Overload t -> [t]
overTypes = map snd . overArgs

-- Lambda lifting: IR to Lifted IR conversion

emptyProg :: Prog
emptyProg = Prog Map.empty Map.empty Set.empty Map.empty Map.empty Map.empty []

prog :: [Ir.Decl] -> IO Prog
prog decls = check $ flip execState emptyProg $ do
  modify $ \p -> p { progGlobals = foldl decl_vars Set.empty decls }
  mapM_ decl decls
  modify $ \p -> p { progDefinitions = reverse (progDefinitions p) }
  p <- get
  mapM_ datatype (Map.toList (progDatatypes p))
  where
  datatype :: (CVar, Datatype) -> State Prog ()
  datatype (tc, Data _ _ cases) = mapM_ f cases where
    f :: (Loc CVar, [TypeSet]) -> State Prog ()
    f (c,tyl) = do
      modify $ \p -> p { progConses = Map.insert (unLoc c) tc (progConses p) }
      case tyl of
        [] -> definition [c] (Cons (unLoc c) [])
        _ -> function (unLoc c) vl (Cons (unLoc c) (map Var vl)) where
          vl = take (length tyl) standardVars

-- Check for duplicate statements
check :: Prog -> IO Prog
check prog = foldM st Map.empty (progDefinitions prog) >. prog where
  st env (Def vl _) = foldM sv env vl
  sv env (Loc l v) = case Map.lookup v env of
    Nothing -> return $ Map.insert v l env
    Just l' -> die (show l++": duplicate definition of '"++(pshow v)++"', previously declared at "++show l')

decl_vars :: Set Var -> Ir.Decl -> Set Var
decl_vars s (Ir.LetD (Loc _ v) _) = Set.insert v s
decl_vars s (Ir.LetM vl _) = foldl (flip Set.insert) s (map unLoc vl)
decl_vars s (Ir.Over (Loc _ v) _ _) = Set.insert v s
decl_vars s (Ir.Data _ _ _) = s

-- |Statements are added in reverse order
decl :: Ir.Decl -> State Prog ()
decl (Ir.LetD v e@(Ir.Lambda _ _)) = do
  let (vl,e') = unwrapLambda e
  e <- expr (Set.fromList vl) e'
  function (unLoc v) vl e
decl (Ir.Over v t e) = do
  let (tl,r,vl,e') = unwrapTypeLambda t e
  e <- expr (Set.fromList vl) e'
  overload (unLoc v) tl r vl e
decl (Ir.LetD v e) = do
  e <- expr Set.empty e
  definition [v] e
decl (Ir.LetM vl e) = do
  e <- expr Set.empty e
  definition vl e
decl (Ir.Data (Loc l tc) tvl cases) =
  modify $ \p -> p { progDatatypes = Map.insert tc (Data l tvl cases) (progDatatypes p) }

-- |Add a toplevel statement
definition :: [Loc Var] -> Exp -> State Prog ()
definition vl e = modify $ \p -> p { progDefinitions = (Def vl e) : progDefinitions p }

-- |Add a global overload
overload :: Var -> [TypeSetArg] -> TypeSet -> [Var] -> Exp -> State Prog ()
overload v tl r vl e | length vl == length tl = modify $ \p -> p { progFunctions = Map.insertWith (++) v [Over tl r vl (Just e)] (progFunctions p) }
overload v tl _ vl _ = error ("overload arity mismatch for "++(pshow v)++": argument types "++show (prettylist tl)++", variables "++show (prettylist vl)) 

-- |Add an unoverloaded global function
function :: Var -> [Var] -> Exp -> State Prog ()
function v vl e = overload v (map ((,) Nothing) tl) r vl e where
  (tl,r) = generalType vl

-- |Unwrap a lambda as far as we can
unwrapLambda :: Ir.Exp -> ([Var], Ir.Exp)
unwrapLambda (Ir.Lambda v e) = (v:vl, e') where
  (vl, e') = unwrapLambda e
unwrapLambda (Ir.ExpLoc _ e) = unwrapLambda e
unwrapLambda e = ([], e)

generalType :: [a] -> ([TypeSet], TypeSet)
generalType vl = (tl,r) where
  r : tl = map TsVar (take (length vl + 1) standardVars)

-- |Unwrap a type/lambda combination as far as we can
unwrapTypeLambda :: TypeSet -> Ir.Exp -> ([TypeSetArg], TypeSet, [Var], Ir.Exp)
unwrapTypeLambda (TsFun t tl) (Ir.Lambda v e) = (typeArg t:tl', r, v:vl, e') where
  (tl', r, vl, e') = unwrapTypeLambda tl e
unwrapTypeLambda t e = ([], t, [], e)

-- |Lambda lift an expression
expr :: Set Var -> Ir.Exp -> State Prog Exp
expr locals (Ir.Let v e@(Ir.Lambda _ _) rest) = do
  e <- lambda locals v e
  rest <- expr (Set.insert v locals) rest
  return $ Let v e rest
expr locals e@(Ir.Lambda _ _) = lambda locals (V "f") e
expr _ (Ir.Int i) = return $ Int i
expr _ (Ir.Chr c) = return $ Chr c
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
expr locals (Ir.Prim prim el) = do
  el <- mapM (expr locals) el
  return $ Prim prim el
expr locals (Ir.Bind v e rest) = do
  e <- expr locals e
  rest <- expr (Set.insert v locals) rest
  return $ Bind v e rest
expr locals (Ir.Return e) = Return =.< expr locals e
expr locals (Ir.PrimIO p el) = PrimIO p =.< mapM (expr locals) el
expr locals (Ir.Spec e t) = expr locals e >.= \e -> Spec e t
expr locals (Ir.ExpLoc l e) = ExpLoc l =.< expr locals e

-- |Lift a single lambda expression
lambda :: Set Var -> Var -> Ir.Exp -> State Prog Exp
lambda locals v e = do
  f <- freshenM v -- use the suggested function name
  let (vl,e') = unwrapLambda e
  e <- expr (foldl (flip Set.insert) locals vl) e'
  let vs = free locals e
  function f (vs ++ vl) e
  return $ foldl Apply (Var f) (map Var vs)

-- |Generate a fresh variable
freshenM :: Var -> State Prog Var
freshenM v = do
  p <- get
  let v' = freshen (progGlobals p) v
  put $ p { progGlobals = Set.insert v' (progGlobals p) }
  return v'

-- |Compute the list of free variables in an expression
free :: Set Var -> Exp -> [Var]
free locals e = Set.toList (Set.intersection locals (f e)) where
  f :: Exp -> Set Var
  f (Int _) = Set.empty
  f (Chr _) = Set.empty
  f (Var v) = Set.singleton v
  f (Apply e1 e2) = Set.union (f e1) (f e2)
  f (Let v e rest) = Set.union (f e) (Set.delete v (f rest))
  f (Cons _ el) = Set.unions (map f el)
  f (Case e pl def) = Set.unions (f e
    : maybe [] (\ (v,e) -> [Set.delete v (f e)]) def
    ++ [f e Set.\\ Set.fromList vl | (_,vl,e) <- pl])
  f (Prim _ el) = Set.unions (map f el)
  f (Bind v e rest) = Set.union (f e) (Set.delete v (f rest))
  f (Return e) = f e
  f (PrimIO _ el) = Set.unions (map f el)
  f (Spec e _) = f e
  f (ExpLoc _ e) = f e

-- |Merge two programs into one

union :: Prog -> Prog -> Prog
union p1 p2 = Prog
  { progDatatypes = Map.unionWithKey conflict (progDatatypes p2) (progDatatypes p1)
  , progFunctions = Map.unionWith (++) (progFunctions p1) (progFunctions p2)
  , progGlobals = Set.union (progGlobals p1) (progGlobals p2)
  , progConses = Map.unionWithKey conflict (progConses p2) (progConses p1)
  , progOverloads = Map.unionWithKey conflict (progOverloads p2) (progOverloads p1)
  , progGlobalTypes = Map.unionWithKey conflict (progGlobalTypes p2) (progGlobalTypes p1)
  , progDefinitions = progDefinitions p1 ++ progDefinitions p2 }
  where
  conflict v _ _ = error ("conflicting datatype declarations for "++(pshow v))

-- Pretty printing

instance Pretty Prog where
  pretty prog = vcat $
       [pretty "-- datatypes"]
    ++ [pretty (Ir.Data (Loc l t) vl c) | (t,Data l vl c) <- Map.toList (progDatatypes prog)]
    ++ [pretty "-- functions"]
    ++ [function v tl r vl e | (v,o) <- Map.toList (progFunctions prog), Over tl r vl e <- o]
    ++ [pretty "-- overloads"]
    ++ [pretty (progOverloads prog)]
    ++ [pretty "-- definitions"]
    ++ map definition (progDefinitions prog)
    where
    function :: Var -> [TypeSetArg] -> TypeSet -> [Var] -> Maybe Exp -> Doc
    function v tl r _ Nothing =
      pretty v <+> pretty "::" <+> hsep (intersperse (pretty "->") (map (guard 2) (tl++[(Nothing,r)])))
    function v tl r vl (Just e) =
      function v tl r vl Nothing $$
      prettylist (v : vl) <+> equals <+> nest 2 (pretty e)
    definition (Def vl e) =
      hcat (intersperse (pretty ", ") (map pretty vl)) <+> equals <+> nest 2 (pretty e)

instance Pretty Exp where
  pretty' = pretty' . revert

instance Pretty (Map Var Overloads) where
  pretty info = vcat [pr f tl o | (f,p) <- Map.toList info, (tl,o) <- Ptrie.toList p] where
    pr f tl (Over _ r _ Nothing) = pretty f <+> prettylist tl <+> pretty "::" <+> pretty r
    pr f tl o@(Over _ _ vl (Just e)) = pr f tl o{ overBody = Nothing } $$
      prettylist (f : vl) <+> equals <+> nest 2 (pretty e)

revert :: Exp -> Ir.Exp
revert (Int i) = Ir.Int i
revert (Chr c) = Ir.Chr c
revert (Var v) = Ir.Var v
revert (Apply e1 e2) = Ir.Apply (revert e1) (revert e2)
revert (Let v e rest) = Ir.Let v (revert e) (revert rest)
revert (Cons c el) = Ir.Cons c (map revert el)
revert (Case e pl def) = Ir.Case (revert e) [(c,vl,revert e) | (c,vl,e) <- pl] (fmap (\ (v,e) -> (v,revert e)) def)
revert (Prim prim el) = Ir.Prim prim (map revert el)
revert (Bind v e rest) = Ir.Bind v (revert e) (revert rest)
revert (Return e) = Ir.Return (revert e)
revert (PrimIO p el) = Ir.PrimIO p (map revert el)
revert (Spec e t) = Ir.Spec (revert e) t
revert (ExpLoc l e) = Ir.ExpLoc l (revert e)
