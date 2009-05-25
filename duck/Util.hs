-- Duck utility functions

module Util
  ( debug
  , foldmap
  , groupPairs
  , die
  , Stack(..)
  , (++.)
  , splitStack
  , (>>=.), (=<<.)
  ) where

import System.IO
import System.Exit
import System.IO.Unsafe
import Data.Function
import Data.List

debug :: Show a => a -> b -> b
debug a b =
  unsafePerformIO (print a >> return b)

foldmap :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
foldmap _ x [] = (x,[])
foldmap f x (h:t) = (x'',h':t') where
  (x',h') = f x h
  (x'',t') = foldmap f x' t

-- Note: it'd be nice if this was linear time, or at least O(n log n)
-- See http://lambda-the-ultimate.org/node/3277
groupPairs :: Eq a => [(a,b)] -> [(a,[b])]
groupPairs pairs = map squash groups where
  squash l = (fst (head l), map snd l)
  groups = groupBy ((==) `on` fst) pairs

die :: String -> IO a
die s = do
  hPutStrLn stderr s
  exitFailure

-- Stacks are lists with an extra bit of information at the bottom
-- This is useful to represent stacks with different layers of types
data Stack a b
  = Base b
  | a :. Stack a b

-- append a list and a stack
(++.) :: [a] -> Stack a b -> Stack a b
(++.) [] r = r
(++.) (h:t) r = h :. (t ++. r)

instance (Show a, Show b) => Show (Stack a b) where
  show s = '[' : concat (intersperse "," (map show a)) ++ " . " ++ show b ++ "]" where
    (a,b) = splitStack s

splitStack :: Stack a b -> ([a],b)
splitStack (Base b) = ([],b)
splitStack (a :. s) = (a:l,b) where
  (l,b) = splitStack s

-- Some convenient extra monad operators

infixl 1 >>=.
infixr 1 =<<.

(>>=.) :: Monad m => m a -> (a -> b) -> m b
m >>=. f = m >>= return . f

(=<<.) :: Monad m => (a -> b) -> m a -> m b
(=<<.) = flip (>>=.)
