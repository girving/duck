{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, BangPatterns #-}
-- | Duck utility functions

module Util
  (
  -- * IO
    exit
  , die
  , debug
  , debugVal
  -- * Data
  -- ** List
  , unique
  , groupPairs
  , spanJust
  , zipCheck
  , zipWithCheck
  -- ** Map
  , insertList
  -- ** Stack
  , Stack(..)
  , (++.)
  , splitStack
  -- * Functionals
  , (...), uncurry3
  , first, second
  , left, right
  -- * Monad
  , nop
  , (>.), (>.=), (>=.)
  , (<<), (.<), (=.<), (.=<)
  , foldM1
  , zipWith3M
  -- ** Error and Exception
  , tryError
  , MonadInterrupt, handleE
  -- ** Strict Identity
  , Sequence, runSequence
  ) where

import System.IO
import System.Exit
import Data.Function
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Exception
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import qualified Control.Monad.Trans.Reader as Reader
import qualified Control.Monad.Trans.State as State
import Debug.Trace

debug :: Show a => a -> b -> b
debug = traceShow

debugVal :: Show a => a -> a
debugVal a = debug a a

unique :: Eq a => [a] -> Maybe a
unique (x:l) | all (x ==) l = Just x
unique _ = Nothing

-- |'group' on keyed pairs.
groupPairs :: Eq a => [(a,b)] -> [(a,[b])]
groupPairs pairs = map squash groups where
  squash l = (fst (head l), map snd l)
  groups = groupBy ((==) `on` fst) pairs

-- |Return the longest prefix that is Just, and the rest.
spanJust :: (a -> Maybe b) -> [a] -> ([b],[a])
spanJust _ [] = ([],[])
spanJust f l@(x:r) = maybe ([],l) (\y -> first (y:) $ spanJust f r) $ f x

-- |Same as 'zip', but bails if the lists aren't equal size
zipCheck :: MonadPlus m => [a] -> [b] -> m [(a,b)]
zipCheck [] [] = return []
zipCheck (x:xl) (y:yl) = ((x,y) :) =.< zipCheck xl yl
zipCheck _ _ = mzero

zipWithCheck :: MonadPlus m => (a -> b -> c) -> [a] -> [b] -> m [c]
zipWithCheck f x y = map (uncurry f) =.< zipCheck x y

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) f g x y = f (g x y)

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (a,b,c) = f a b c

zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f x y z = mapM (uncurry3 f) (zip3 x y z)

-- more efficient than Arrow instances:
first :: (a -> c) -> (a,b) -> (c,b)
first f (a,b) = (f a,b)
second :: (b -> c) -> (a,b) -> (a,c)
second f (a,b) = (a,f b)

left :: (a -> c) -> Either a b -> Either c b
left f (Left a) = Left (f a)
left _ (Right b) = Right b
right :: (b -> c) -> Either a b -> Either a c
right _ (Left a) = Left a
right f (Right b) = Right (f b)

-- |Insert a set of unzipped key-value pairs into a Map
insertList :: Ord k => Map k v -> [k] -> [v] -> Map k v
insertList !m [] [] = m
insertList !m (k:ks) (v:vs) = insertList (Map.insert k v m) ks vs
insertList !_ _ _ = error "different lengths in Util.insertList"

exit :: Int -> IO a
exit 0 = exitSuccess
exit i = exitWith (ExitFailure i)

-- |Print a string on stderr and exit with the given value
die :: MonadIO m => Int -> String -> m a
die i s = liftIO $ do
  hPutStrLn stderr s
  exit i

-- |Stacks are lists with an extra bit of information at the bottom
-- This is useful to represent stacks with different layers of types
data Stack a b
  = Base b
  | a :. Stack a b

-- |append a list and a stack
(++.) :: [a] -> Stack a b -> Stack a b
(++.) [] r = r
(++.) (h:t) r = h :. (t ++. r)

instance (Show a, Show b) => Show (Stack a b) where
  show s = '[' : intercalate "," (map show a) ++ " . " ++ show b ++ "]" where
    (a,b) = splitStack s

splitStack :: Stack a b -> ([a],b)
splitStack (Base b) = ([],b)
splitStack (a :. s) = (a:l,b) where
  (l,b) = splitStack s

-- Some convenient extra monad operators

infixl 1 >., >.=, >=.
infixr 1 <<, .<, =.<, .=<
(>.) :: Monad m => m a -> b -> m b
(.<) :: Monad m => b -> m a -> m b
(<<) :: Monad m => m b -> m a -> m b
(>.=) :: Monad m => m a -> (a -> b) -> m b
(=.<) :: Monad m => (a -> b) -> m a -> m b
(>=.) :: Monad m => (a -> m b) -> (b -> c) -> a -> m c
(.=<) :: Monad m => (b -> c) -> (a -> m b) -> a -> m c

(>.) e r = e >> return r
(.<) r e = e >> return r -- <$
(<<) r e = e >> r
(>.=) e r = e >>= return . r
(=.<) r e = e >>= return . r -- fmap, <$>, liftM
(>=.) e r = e >=> return . r
(.=<) r e = e >=> return . r

nop :: Monad m => m ()
nop = return ()

foldM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldM1 f (h:t) = foldM f h t
foldM1 _ [] = error "foldM1 applied to an empty list"

tryError :: (MonadError e m, Error e) => m a -> m (Either e a)
tryError f = catchError (Right =.< f) (return . Left)

-- A monad for asynchronously interruptible computations
-- I.e., the equivalent of handle for general monads

class Monad m => MonadInterrupt m where
  catchE :: Exception e => m a -> (e -> m a) -> m a

handleE :: (MonadInterrupt m, Exception e) => (e -> m a) -> m a -> m a
handleE = flip catchE

instance MonadInterrupt IO where 
  catchE = catchE

instance MonadInterrupt m => MonadInterrupt (ReaderT r m) where 
  catchE = Reader.liftCatch catchE 

instance MonadInterrupt m => MonadInterrupt (StateT s m) where 
  catchE = State.liftCatch catchE

instance (MonadInterrupt m, Error e) => MonadInterrupt (ErrorT e m) where 
  catchE = flip $ mapErrorT . handleE . (runErrorT .)

-- |Strict identity monad, similar (but not identical) to Control.Parallel.Strategies.Eval
newtype Sequence a = Sequence { runSequence :: a }

instance Functor Sequence where
  fmap f = Sequence . f . runSequence

instance Monad Sequence where
  return = Sequence
  m >>= k = k $! runSequence m
  m >> k = seq (runSequence m) k
