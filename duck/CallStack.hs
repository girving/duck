{-# LANGUAGE TypeSynonymInstances #-}
-- | Duck call stack type
--
-- Used to maintain the current position to display stack traces in errors.

module CallStack
  ( CallStack
  , CallFrame(..)
  , mapStackArgs
  ) where

import Var
import Pretty
import SrcLoc

-- |Represents a single function call with the given type of arguments.
data CallFrame a = CallFrame
  { callFunction :: Var
  , callArgs :: [a]
  , callLoc :: SrcLoc
  }

type CallStack a = [CallFrame a]

instance Pretty a => Pretty (CallStack a) where
  pretty s = h $$ nest 2 (vcat $ reverse $ map p s) where
    h = pretty "Traceback (most recent call last):"
    p (CallFrame f args loc) = pretty (show loc) <> pretty ":" <+> pretty f <+> prettylist args

instance Functor CallFrame where
  fmap f c = c { callArgs = map f (callArgs c) }

mapStackArgs :: (a -> b) -> CallStack a -> CallStack b
mapStackArgs f = map $ fmap f
