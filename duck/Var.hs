-- Duck Variables

module Var where

import Pretty
import Text.PrettyPrint
import Data.Char
import Data.List

newtype Var = V String

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

precedence :: Var -> Maybe Int
precedence (V op) = case head op of
  '+' -> Just 20
  '-' -> Just 20
  '*' -> Just 30
  '/' -> Just 30 
  _ -> Nothing
