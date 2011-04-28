{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

-- For now, this is dynamically typed

module Memory
  ( Value(..)
  , Convert(..)
  ) where

-- Pull in definition of Value
import Gen.Memory

-- Add instance declarations
deriving instance Show Value

-- Typed values

class Convert t where
  value :: t -> Value
  unvalue :: Value -> t

instance Convert Value where
  value x = x
  unvalue x = x

instance Convert Int where
  value = ValInt
  unvalue v = let ValInt i = v in i

instance Convert Char where
  value = ValChar
  unvalue v = let ValChar c = v in c

instance Convert a => Convert [a] where
  value [] = ValCons 0 []
  value (x:l) = ValCons 1 [value x,value l]
  unvalue (ValCons 0 []) = []
  unvalue (ValCons 1 [x,l]) = unvalue x : unvalue l
  unvalue _ = undefined

instance Convert a => Convert (Maybe a) where
  value Nothing = ValCons 0 []
  value (Just x) = ValCons 1 [value x]
  unvalue (ValCons 0 []) = Nothing
  unvalue (ValCons 1 [x]) = Just (unvalue x)
  unvalue _ = undefined

instance (Convert a, Convert b) => Convert (a,b) where
  value (a,b) = ValCons 0 [value a, value b]
  unvalue (ValCons 0 [a,b]) = (unvalue a, unvalue b)
  unvalue _ = undefined

instance (Convert a, Convert b, Convert c) => Convert (a,b,c) where
  value (a,b,c) = ValCons 0 [value a, value b, value c]
  unvalue (ValCons 0 [a,b,c]) = (unvalue a, unvalue b, unvalue c)
  unvalue _ = undefined
