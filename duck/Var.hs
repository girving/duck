{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | Duck Variables

module Var 
  ( Var(..)
  , CVar
  , ModuleName
  , InScopeSet
  , Precedence
  , Fixity(..)
  , PrecFix
  , PrecEnv
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
  -- ** Pretty printing helpers
  , precedence
  ) where

import Pretty
import Data.Char
import Data.List

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)

newtype Var = V { unV :: String } deriving (Eq, Ord)
type CVar = Var
type ModuleName = String

type Precedence = Int
data Fixity = LeftFix | NonFix | RightFix deriving (Eq, Show, Ord)
type PrecFix = (Precedence, Fixity)
type PrecEnv = Map Var PrecFix

instance Show Var where
  show (V s) = show s

instance Pretty Var where
  pretty' (V v) =
    (case v of
      c:_ | isAlpha c || c == '_' || c == '(' || c == '[' -> pretty'
      _ -> pretty' . parens) v

type InScopeSet = Set Var

instance Pretty Fixity where
  pretty LeftFix = pretty "infixl"
  pretty RightFix = pretty "infixr"
  pretty NonFix = pretty "infix"

instance Pretty PrecFix where
  pretty (p,d) = pretty d <+> pretty p

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

precedence :: Var -> Maybe Int
precedence (V op) = case head op of
  '+' -> Just 20
  '-' -> Just 20
  '*' -> Just 30
  '/' -> Just 30 
  _ -> Nothing

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
