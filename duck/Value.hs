{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
-- | Duck interpreter values

module Value
  ( Env
  , module Gen.Value
  , valEmpty
  ) where

import Prelude hiding (lookup)

import Data.Map (Map)

import Var
import Memory

-- Pull in definition of FunValue
import Gen.Value

-- Add instance declarations
deriving instance Show FunValue

type Env = Map Var Value

valEmpty :: Value
valEmpty = valCons 0 []
