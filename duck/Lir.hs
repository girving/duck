{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck Lifted Intermediate Representation
--
-- "Lir" is the same as "Ir" except that:
-- 'Exp' is unchanged except that 'Lambdas' have all been lifted to top-level functions.
-- Top-level declarations have been organized and mapped.

module Lir
  ( Prog(..)
  , ProgMonad(..)
  , Datatype(..), Overload(..), Definition(..)
  , Overloads
  , Exp(..)
  , freeOf
  , overTypes
  , empty
  , union
  , check
  , lirError, dupError
  , complete
  ) where

import Prelude hiding (mapM)
import Data.Maybe
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM, guard)

import Util
import Var
import SrcLoc
import Ptrie (Ptrie)
import Pretty
import Stage
import Type

-- Pull in definition of Exp and add a Show instance
import Gen.Lir
deriving instance Show Exp

-- Lifted IR data structures

data Prog = Prog
  { progName :: ModuleName
  , progDatatypes :: Map CVar Datatype -- ^ all datatypes by type constructor
  , progFunctions :: Map Var [Overload TypePat] -- ^ original overload definitions by function name
  , progConses :: Map CVar CVar -- ^ map data constructors to datatypes (type inference will make this go away)
  , progOverloads :: Map Var Overloads -- ^ all overloads inferred to be needed, set after inference
  , progGlobalTypes :: TypeEnv -- ^ set after inference
  , progDefinitions :: [Definition] -- ^ list of top-level definitions
  }

-- |Overload definition, parameterized by either 'Type' or 'TypePat', depending on whether it is a specific resolution, or the original definition
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
type Overloads = Ptrie TypeVal Trans (Overload TypeVal)

-- |Top-level variable definition: @(VARs) = EXP@
data Definition = Def
  { defVars :: [Loc Var] -- (tuple of) variables to assign
  , defBody :: Exp -- definition
  }
instance HasLoc Definition where loc = loc . defVars

class Monad m => ProgMonad m where
  getProg :: m Prog

instance HasVar Exp where
  var = ExpVar
  unVar (ExpVar v) = Just v
  unVar (ExpLoc _ e) = unVar e
  unVar _ = Nothing

-- |Type of arguments an overload expects to be passed (as opposed to expects to recieve)
overTypes :: Overload t -> [t]
overTypes = map snd . overArgs

-- Lambda lifting: IR to Lifted IR conversion

lirError :: Pretty s => SrcLoc -> s -> a
lirError l = fatal . locMsg l

dupError :: Pretty v => v -> SrcLoc -> SrcLoc -> a
dupError v n o = lirError n $ "duplicate definition of" <+> quoted v <> (", previously declared at" <&+> o)

empty :: ModuleName -> Prog
empty n = Prog n Map.empty Map.empty Map.empty Map.empty Map.empty []

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
    let add s (L _ (V "_")) = return s
        add s (L l v) = do
          maybe nop (dupError v l) $ Map.lookup v s
          return $ Map.insert v l s
    s <- foldM add s vl
    expr (Set.union (Map.keysSet s) types) body
    return s
  funs s (f,fl) = mapM_ fun fl where
    fun (Over l _ _ vl body) = do
      when (vl == []) $ lirError l $ "overload" <+> quoted f <+> "has no arguments"
      vs <- foldM (\s v -> do
        when (Set.member v s) $ lirError l $ quoted v <+> "appears more than once in argument list for" <+> quoted f
        return $ addVar v s) Set.empty vl
      maybe nop (expr (Set.union s vs)) body
  expr s = mapM_ (\(v,l) -> lirError l $ quoted v <+> "undefined") . free s noLoc
  datatype (_, d) = mapM_ cons (dataConses d) where
    cons (L l c,tl) = case Set.toList $ Set.fromList (concatMap freeVars tl) Set.\\ Set.fromList (dataTyVars d) of
      [] -> success
      [v] -> lirError l $ "variable" <+> quoted v <+> "is unbound in constructor" <+> quoted (TsCons c tl)
      fv -> lirError l $ "variables" <+> quoted (hsep fv) <+> "are unbound in constructor" <+> quoted (TsCons c tl)

-- |Compute the list of free variables in an expression
freeOf :: InScopeSet -> Exp -> [Var]
freeOf locals e = Set.toList (Set.intersection locals (f e)) where
  f = Set.fromList . map fst . free Set.empty noLoc

free :: InScopeSet -> SrcLoc -> Exp -> [(Var,SrcLoc)]
free _ _ (ExpVar (V "_")) = []
free s l (ExpVar v)
  | Set.notMember v s = [(v,l)]
  | otherwise = []
free _ _ (ExpVal _ _) = []
free s l (ExpApply e1 e2) = free s l e1 ++ free s l e2
free s l (ExpLet v e c) = free s l e ++ free (addVar v s) l c
free s l (ExpCons _ el) = concatMap (free s l) el
free s l (ExpCase v al d) =
  free s l (ExpVar v)
  ++ concatMap (\(_,vl,e) -> free (foldr addVar s vl) l e) al
  ++ maybe [] (free s l) d
free s l (ExpPrim _ el) = concatMap (free s l) el
free s l (ExpBind v e c) = free s l e ++ free (addVar v s) l c
free s l (ExpReturn e) = free s l e
free s l (ExpSpec e _) = free s l e
free s _ (ExpLoc l e) = free s l e

-- |Merge two programs into one

union :: Prog -> Prog -> Prog
union p1 p2 = Prog
  { progName = progName p2 -- use the second module's name
  , progDatatypes = Map.unionWithKey conflictLoc (progDatatypes p2) (progDatatypes p1)
  , progFunctions = Map.unionWith (++) (progFunctions p1) (progFunctions p2)
  , progConses = Map.unionWithKey conflict (progConses p2) (progConses p1) -- XXX overloaded constructors?
  , progOverloads = Map.unionWithKey conflict (progOverloads p2) (progOverloads p1) -- XXX cross-module overloads?
  , progGlobalTypes = Map.unionWithKey conflict (progGlobalTypes p2) (progGlobalTypes p1)
  , progDefinitions = progDefinitions p1 ++ progDefinitions p2 }
  where
  conflictLoc v n o = dupError v (loc n) (loc o)
  conflict v _ _ = dupError v noLoc noLoc

-- |Fill in progConses and add a creation overload for each datatype constructor
complete :: Prog -> Prog
complete prog = flip execState prog $ mapM_ datatype (Map.elems $ progDatatypes prog) where
  datatype :: Datatype -> State Prog ()
  datatype d = mapM_ f (dataConses d) where
    f :: (Loc CVar, [TypePat]) -> State Prog ()
    f (c,tyl) = do
      modify $ \p -> p { progConses = Map.insert (unLoc c) (dataName d) (progConses p) }
      case tyl of
        [] -> modify $ \p -> p { progDefinitions = Def [c] (ExpCons (unLoc c) []) : progDefinitions p }
        _ -> overload c tl r vl (ExpCons (unLoc c) (map ExpVar vl)) where
          vl = take (length tyl) standardVars
          (tl,r) = generalType vl

-- |Add a global overload
overload :: Loc Var -> [TypePat] -> TypePat -> [Var] -> Exp -> State Prog ()
overload (L l v) tl r vl e | length vl == length tl = modify $ \p -> p { progFunctions = Map.insertWith (++) v [Over l (map ((,) NoTrans) tl) r vl (Just e)] (progFunctions p) }
overload (L l v) tl _ vl _ = lirError l $ "overload arity mismatch for" <+> quoted v <:> "argument types" <+> quoted (hsep tl) <> ", variables" <+> quoted (hsep vl)
