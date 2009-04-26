-- Duck Variables

module Var where

import Pretty
import Text.PrettyPrint
import Data.Char
import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

newtype Var = V String
type CVar = Var

instance Show Var where
  show (V s) = show s

instance Pretty Var where
  pretty' (V v) = (100,
    let c = head v in
    if isAlpha c || c == '_' then
      text v
    else parens $ text v)

instance Eq Var where
  (==) (V a) (V b) = a == b

instance Ord Var where
  compare (V a) (V b) = compare a b

type InScopeSet = Set Var
  
freshen :: InScopeSet -> Var -> Var
freshen scope v = search v where
  search v | Set.notMember v scope = v
           | V s <- v = search (V $ s ++ show size)
  size = Set.size scope

fresh :: InScopeSet -> Var
fresh s = freshen s (V "x")

freshVars :: InScopeSet -> Int -> (InScopeSet, [Var])
freshVars s 0 = (s, [])
freshVars s n = (s', v : vl) where 
  v = fresh s
  (s', vl) = freshVars (Set.insert v s) (n-1)

standardVars :: [Var]
standardVars = letters ++ others where
  letters = [V [x] | x <- "abcdefghijklmnopqrstuvwxyz"]
  others = [V ("t" ++ show i) | i <- [1..]]

ignored = V "_"

precedence :: Var -> Maybe Int
precedence (V op) = case head op of
  '+' -> Just 20
  '-' -> Just 20
  '*' -> Just 30
  '/' -> Just 30 
  _ -> Nothing


tuple :: [a] -> Var
tuple [] = V "()"
tuple x = V (replicate (length x - 1) ',')

istuple :: Var -> Bool
istuple (V s) = all (',' ==) s

tuplelen :: Var -> Maybe Int
tuplelen (V s) | istuple (V s) = Just (1 + length s)
tuplelen _ = Nothing
