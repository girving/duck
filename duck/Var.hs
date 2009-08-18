{-# LANGUAGE PatternGuards #-}
-- | Duck Variables

module Var 
  ( Var(..)
  , CVar
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
  , ignored
  , precedence
  , tupleCons
  , istuple
  , tuplelen
  , isCons
  ) where

import Pretty
import Data.Char
import Data.List

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)

newtype Var = V String deriving (Eq, Ord)
type CVar = Var

type Precedence = Int
data Fixity = LeftFix | NonFix | RightFix deriving (Eq, Show, Ord)
type PrecFix = (Precedence, Fixity)
type PrecEnv = Map Var PrecFix

instance Show Var where
  show (V s) = show s

instance Pretty Var where
  pretty' (V v) = (100,
    let c = head v in
    if isAlpha c || c == '_' || c == '(' || c == '[' then
      pretty v
    else parens $ pretty v)

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

ignored :: Var
ignored = V "_"

precedence :: Var -> Maybe Int
precedence (V op) = case head op of
  '+' -> Just 20
  '-' -> Just 20
  '*' -> Just 30
  '/' -> Just 30 
  _ -> Nothing


tupleCons :: [a] -> Var
tupleCons [] = V "()"
tupleCons [_] = error "no singleton tuples"
tupleCons (_:l) = V ([',' | _ <- l])

istuple :: Var -> Bool
istuple (V s) = all (',' ==) s

tuplelen :: Var -> Maybe Int
tuplelen (V s) | istuple (V s) = Just (1 + length s)
tuplelen _ = Nothing

isCons :: Var -> Bool
isCons (V (c:_)) | isUpper c || elem c "([:," = True
isCons _ = False
