{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}
-- | Duck Lifted Intermediate Representation
--
-- "Lir" is the same as "Ir" except that:
-- 1. 'Exp' is unchanged except that 'Lambdas' have all been lifted to top-level functions.
-- 2. Top-level declarations have been organized and mapped.
-- 3. ExpVar is replaced with one of ExpLocal, ExpGlobal, or ExpValue, depending on what kind of variable it is.

module Lir
  ( Prog(..)
  , ProgMonad(..)
  , Overload(..), Definition(..)
  , Overloads
  , GlobalType, GlobalTypes
  , Exp(..)
  , Atom(..)
  , Kind(..), Globals
  , expLocal, expGlobal, expVal
  , free
  , overTypes
  , empty
  , union
  , check
  , globals
  , kindConflict
  , lirError, dupError
  , complete
  , addOverload
  ) where

import Prelude hiding (mapM)

import Control.Monad.State hiding (mapM)
import Data.List hiding (union)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Memory
import Pretty
import Ptrie (Ptrie)
import qualified Ptrie as Ptrie
import SrcLoc
import Stage
import Type
import TypedValue ()
import Util
import Var

-- Pull in definition of Exp and add a Show instance
import Gen.Lir
deriving instance Show Exp
deriving instance Show Atom

-- Lifted IR data structures

data Prog = Prog
  { progName :: ModuleName
  , progDatatypes :: Map CVar Datatype -- ^ all datatypes by type constructor
  , progOverloads :: Map Var Overloads -- ^ all overloads definitions and inferred expansions
  , progGlobalTypes :: GlobalTypes -- ^ set after inference
  , progDefinitions :: [Definition] -- ^ list of top-level definitions
  }

-- |Overload definition, parameterized by either 'Type' or 'TypePat', depending on whether it is a specific resolution, or the original definition
data Overload t = Over
  { overLoc :: SrcLoc
  , overArgs :: [TransType t] -- ^ Type of arguments with transform annotations
  , overRet :: !t -- ^ Type of return value
  , overVars :: [Var] -- ^ Names of arguments
  , overBody :: Maybe Exp -- ^ Definition of function, or 'Nothing' if not a fully applied function
  } deriving (Show)
instance HasLoc (Overload t) where loc = overLoc

-- |The main overload table of specific overload resolutions used by the program.
-- Note that there may be many more entries than actual overload definitions, since every specific set of argument types creates a new overload.
type Overloads = Ptrie TypeVal [Overload TypePat] (Overload TypeVal)

-- |Top-level variable definition: @(VARs) = EXP@
data Definition = Def
  { defStatic :: Bool
  , defVars :: [Loc Var] -- (tuple of) variables to assign
  , defBody :: Exp -- definition
  }
instance HasLoc Definition where loc = loc . defVars

type GlobalType = (TypeVal, (Exp, Maybe Int))
type GlobalTypes = Map Var GlobalType

class Monad m => ProgMonad m where
  getProg :: m Prog

instance HasVar Atom where
  unVar (AtomLocal v) = Just v
  unVar (AtomGlobal v) = Just v
  unVar (AtomVal _) = Nothing

instance HasVar Exp where
  unVar (ExpAtom a) = unVar a
  unVar (ExpLoc _ e) = unVar e
  unVar _ = Nothing

-- |Information about global variables
data Kind
  = GlobalKind
  | StaticKind
  | FunctionKind
  | DatatypeKind
  | VoidKind
  deriving (Show, Eq)

type Globals = Map CVar Kind

expLocal :: Var -> Exp
expLocal = ExpAtom . AtomLocal

expGlobal :: Var -> Exp
expGlobal = ExpAtom . AtomGlobal

expVal :: TypeVal -> Value -> Exp
expVal t v = ExpAtom $ AtomVal $ Any t v

-- |Type of arguments an overload expects to be passed (as opposed to expects to recieve)
overTypes :: Overload t -> [t]
overTypes = map snd . overArgs

-- Lambda lifting: IR to Lifted IR conversion

lirError :: Pretty s => SrcLoc -> s -> a
lirError l = fatal . locMsg l

dupError :: Pretty v => v -> SrcLoc -> SrcLoc -> a
dupError v n o = lirError n $ "duplicate definition of" <+> quoted v <> (", previously declared at" <&+> o)

empty :: ModuleName -> Prog
empty n = Prog n Map.empty Map.empty Map.empty []

-- |A few consistency checks on Lir programs
check :: Prog -> ()
check prog = runSequence $ do
  let fs = Map.map (either loc loc . Ptrie.get) (progOverloads prog)
  fds <- foldM def fs (progDefinitions prog)
  mapM_ (funs (Map.keysSet fds `Set.union` types)) $ Map.toList (progOverloads prog)
  mapM_ datatype (Map.toList $ progDatatypes prog)
  where
  types = Map.keysSet (progDatatypes prog)
  def s (Def _ vl body) = do
    let add s (L _ (V "_")) = return s
        add s (L l v) = do
          maybe nop (dupError v l) $ Map.lookup v s
          return $ Map.insert v l s
    s <- foldM add s vl
    expr (Map.keysSet s `Set.union` types) body
    return s
  funs s (f,fl) = either (mapM_ fun) (const nop) $ Ptrie.get fl where
    fun (Over{ overLoc = l, overVars = vl, overBody = body}) = do
      when (vl == []) $ lirError l $ "overload" <+> quoted f <+> "has no arguments"
      vs <- foldM (\s v -> do
        when (Set.member v s) $ lirError l $ quoted v <+> "appears more than once in argument list for" <+> quoted f
        return $ addVar v s) Set.empty vl
      maybe nop (expr (s `Set.union` vs)) body
  expr s = mapM_ (\(v,l) -> lirError l $ quoted v <+> "undefined") . free' s noLoc
  datatype (_, d) = info $ dataInfo d where
    info (DataAlgebraic conses) = mapM_ cons conses
    info (DataPrim _) = nop
    cons (L l c,tl) = case Set.toList $ Set.fromList (concatMap freeVars tl) Set.\\ Set.fromList (dataTyVars d) of
      [] -> nop
      [v] -> lirError l $ "variable" <+> quoted v <+> "is unbound in constructor" <+> quoted (prettyap c tl)
      fv -> lirError l $ "variables" <+> quoted (hsep fv) <+> "are unbound in constructor" <+> quoted (prettyap c tl)

-- |Compute the set of global symbols in a program
globals :: Prog -> Globals
globals prog = foldl' (Map.unionWithKey kindConflict) Map.empty
  [Map.singleton (V "Void") VoidKind,
   Map.map (const DatatypeKind) $ progDatatypes prog,
   Map.map (const FunctionKind) $ progOverloads prog,
   foldl' (\g (s, v) -> insertVar v (if s then StaticKind else GlobalKind) g) Map.empty $ 
    concatMap (\d -> map ((,) (defStatic d) . unLoc) $ defVars d) $ progDefinitions prog]

kindConflict :: Var -> Kind -> Kind -> Kind
kindConflict v DatatypeKind k | isTuple v = k
kindConflict v k k' | k == k' = k
                    | otherwise = lirError noLoc $ quoted v <+> "is declared as both a" <+> s k <+> "and a" <+> s k'
  where s GlobalKind   = "global"
        s StaticKind   = "static"
        s FunctionKind = "function"
        s DatatypeKind = "datatype"
        s VoidKind     = "datatype"
 
-- |Compute the list of free variables in an expression given the set of in scope variables
free :: InScopeSet -> Exp -> [Var]
free s e = Set.toList $ Set.fromList $ map fst (free' s (noLoc :: SrcLoc) e :: [(Var,SrcLoc)])

free' :: InScopeSet -> SrcLoc -> Exp -> [(Var,SrcLoc)]
free' s l (ExpAtom a) = freeAtom s l a
free' s l (ExpApply e1 e2) = free' s l e1 ++ free' s l e2
free' s l (ExpLet _ v e c) = free' s l e ++ free' (addVar v s) l c
free' s l (ExpCons _ _ el) = concatMap (free' s l) el
free' s l (ExpCase _ a al d) =
  freeAtom s l a
  ++ concatMap (\(_,vl,e) -> free' (foldr addVar s vl) l e) al
  ++ maybe [] (free' s l) d
free' s l (ExpPrim _ el) = concatMap (free' s l) el
free' s l (ExpSpec e _) = free' s l e
free' s _ (ExpLoc l e) = free' s l e

freeAtom :: InScopeSet -> SrcLoc -> Atom -> [(Var,SrcLoc)]
freeAtom s l (AtomLocal v)
  | V "_" <- v = error "unexpected '_' in Lir.freeAtom"
  | Set.notMember v s = [(v,l)]
  | otherwise = []
freeAtom _ _ (AtomGlobal _) = []
freeAtom _ _ (AtomVal _) = []

-- |Merge two programs into one

union :: Prog -> Prog -> Prog
union p1 p2 = Prog
  { progName = progName p2 -- use the second module's name
  , progDatatypes   = Map.unionWithKey conflictLoc          (progDatatypes   p2) (progDatatypes   p1)
  , progOverloads = Map.unionWithKey (Ptrie.unionWith . uf) (progOverloads   p1) (progOverloads   p2)
  , progGlobalTypes = Map.unionWithKey conflict             (progGlobalTypes p2) (progGlobalTypes p1)
  , progDefinitions = progDefinitions p1 ++ progDefinitions p2
  }
  where
  uf _ (Left l1) (Left l2) = Left $ l1 ++ l2
  uf k v1 v2 = conflict k v1 v2
  conflictLoc v n o = dupError v (loc n) (loc o)
  conflict v _ _ = dupError v noLoc noLoc

-- |Given a set of datatypes, add a creation overload for each datatype constructor
complete :: Map CVar Datatype -> Prog -> Prog
complete datatypes prog = flip execState prog $ mapM_ datatype $ Map.elems datatypes where
  datatype :: Datatype -> State Prog ()
  datatype d = info $ dataInfo d where
    info (DataAlgebraic conses) = mapM_ cons (zip [0..] conses)
    info (DataPrim _) = nop
    cons :: (Int, (Loc CVar, [TypePat])) -> State Prog ()
    cons (i,(c,[])) = modify $ \p -> p { progDefinitions = Def False [c] (ExpCons d i []) : progDefinitions p }
    cons (i,(c,tyl)) = overload c tl r vl (ExpCons d i (map expLocal vl)) where
      vl = take (length tyl) standardVars
      (tl,r) = generalType vl

addOverload :: Var -> Overload TypePat -> Prog -> Prog
addOverload f o p = p { progOverloads = Map.insertWith 
  (const $ Ptrie.modify $ \ ~(Left l) -> Left (l ++ [o])) 
  f (Ptrie.empty $ Left [o]) (progOverloads p) }

-- |Add a global overload
overload :: Loc Var -> [TypePat] -> TypePat -> [Var] -> Exp -> State Prog ()
overload (L l f) tl r vl e | length vl == length tl = modify $ addOverload f $ Over l (map ((,) NoTrans) tl) r vl (Just e)
overload (L l v) tl _ vl _ = lirError l $ "overload arity mismatch for" <+> quoted v <:> "argument types" <+> quoted (hsep tl) <> ", variables" <+> quoted (hsep vl)
