{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

module Value
  ( Env
  , FunValue(..), DelayValue(..), IOValue(..)
  , valEmpty
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)

import Var
import Memory

-- Pull in definition of IOValue and FunValue
import Gen.Value

-- Add instance declarations
deriving instance Show FunValue
deriving instance Show IOValue

type Env = Map Var Value

valEmpty :: Value
valEmpty = valCons 0 []
