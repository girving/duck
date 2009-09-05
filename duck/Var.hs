{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | Duck Variables

module Var 
  ( Var(..)
  , CVar
  , ModuleName
  , InScopeSet
  , addVar
  , fresh
  , freshen
  , freshVars
  , standardVars
  , moduleVar
  , HasVar(..)
  -- * Primitive values/variables/constructors
  -- 
  -- These might make more sense in "Prims".
  , ignored
  , tupleCons
  , isTuple
  , tupleLen
  , isCons
  ) where

import Pretty
import Data.Char
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import SrcLoc

newtype Var = V { unV :: String } deriving (Eq, Ord)
type CVar = Var
type ModuleName = String

instance Show Var where
  show (V s) = show s

instance Pretty Var where
  pretty' (V v@(c:_)) | isAlpha c || c `elem` "_([" = pretty' v
  pretty' (V v) = -1 #> v

type InScopeSet = Set Var

addVar :: Var -> InScopeSet -> InScopeSet
addVar (V "_") = id
addVar v = Set.insert v

freshen :: InScopeSet -> Var -> (InScopeSet, Var)
freshen scope v = search v where
  search v | Set.notMember v scope = (Set.insert v scope, v)
           | V s <- v = search (V $ s ++ show size)
  size = Set.size scope

fresh :: InScopeSet -> (InScopeSet, Var)
fresh s = freshen s (V "x")

freshVars :: InScopeSet -> Int -> (InScopeSet, [Var])
freshVars s 0 = (s, [])
freshVars s n = (s'', v : vl) where 
  (s', v) = fresh s
  (s'', vl) = freshVars s' (n-1)

standardVars :: [Var]
standardVars = letters ++ others where
  letters = [V [x] | x <- ['a'..'z']]
  others = [V ("t" ++ show i) | i <- [1..] :: [Int]]

moduleVar :: ModuleName -> Var -> Var
moduleVar m (V v) = V (m ++ '.' : v)

ignored :: Var
ignored = V "_"

tupleCons :: [a] -> Var
tupleCons [] = V "()"
tupleCons [_] = error "no singleton tuples"
tupleCons (_:l) = V ([',' | _ <- l])

isTuple :: Var -> Bool
isTuple (V "()") = True
isTuple (V s) = all (',' ==) s

tupleLen :: Var -> Maybe Int
tupleLen (V "()") = Just 0
tupleLen (V s) | isTuple (V s) = Just (1 + length s)
tupleLen _ = Nothing

isCons :: Var -> Bool
isCons (V (c:_)) | isUpper c || elem c "([:," = True
isCons _ = False


class HasVar a where
  var :: Var -> a
  unVar :: a -> Maybe Var

instance HasVar Var where
  var x = x
  unVar = Just

instance HasVar String where
  var = unV
  unVar = Just . V

instance HasVar a => HasVar (Loc a) where
  var = Loc noLoc . var
  unVar = unVar . unLoc 
