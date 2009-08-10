-- | Duck call stack type

module CallStack
  ( CallStack
  , CallFrame(..)
  , showStack
  , mapStackArgs
  ) where

import Prelude hiding (catch)
import Var
import Pretty
import SrcLoc

data CallFrame a = CallFrame
  { callFunction :: Var
  , callArgs :: [a]
  , callLoc :: SrcLoc
  }

type CallStack a = [CallFrame a]

showStack :: Pretty a => CallStack a -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (CallFrame f args loc) = "  " ++ show loc ++ " in "++(pshow f)++' ' : show (prettylist args)

mapStackArgs :: (a -> b) -> CallStack a -> CallStack b
mapStackArgs f = map (\c -> c { callArgs = map f (callArgs c) })
