-- Duck call stack type

module Callstack
  ( CallFrame(..)
  , Callstack
  , showStack
  ) where

import Prelude hiding (catch)
import SrcLoc
import Var
import Pretty

data CallFrame a = CallFrame 
  { callFunction :: Var
  , callArgs :: [a]
  , callLoc :: SrcLoc
  }

type Callstack a = [CallFrame a]

showStack :: Pretty a => Callstack a -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (CallFrame f args loc) = "  " ++ show loc ++ " in "++show (pretty f)++' ' : show (prettylist args)
