-- Duck utility functions

module Util where

import System.IO.Unsafe

debug :: Show a => a -> b -> b
debug a b =
  seq (unsafePerformIO (print a)) b
