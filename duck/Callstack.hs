-- Duck call stack type

module Callstack
  ( Callstack
  , showStack
  ) where

import Prelude hiding (catch)
import Var
import Pretty

type Callstack a = [(Var, [a])]

showStack :: Pretty a => Callstack a -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (f,args) = "  in "++show (pretty f)++' ' : show (prettylist args)
