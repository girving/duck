{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
-- | Duck utility functions

module Util
  ( debug
  , debugVal
  , foldmap
  , duplicates
  , groupPairs
  , die
  , Stack(..)
  , (++.)
  , splitStack
  , nop
  , (>.), (>.=), (>=.)
  , (=.<), (.=<)
  , foldM1
  , allM
  , firstM
  , secondM
  , MaybeT(..)
  , MonadMaybe(..)
  , success
  , returnIf
  , MonadInterrupt(..)
  , mapMaybeT
  ) where

import System.IO
import System.Exit
import System.IO.Unsafe
import Data.Function
import Data.List
import Control.Exception
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Trans

debug :: Show a => a -> b -> b
debug a b =
  unsafePerformIO (print a >> return b)

debugVal :: Show a => a -> a
debugVal a = unsafePerformIO (print a) `seq` a

foldmap :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
foldmap _ x [] = (x,[])
foldmap f x (h:t) = (x'',h':t') where
  (x',h') = f x h
  (x'',t') = foldmap f x' t

-- |Find all entries that occur more than once
duplicates :: Eq a => [a] -> [a]
duplicates l = l \\ nub l

-- Note: it'd be nice if this was linear time, or at least O(n log n)
-- See http://lambda-the-ultimate.org/node/3277
groupPairs :: Eq a => [(a,b)] -> [(a,[b])]
groupPairs pairs = map squash groups where
  squash l = (fst (head l), map snd l)
  groups = groupBy ((==) `on` fst) pairs

die :: MonadIO m => String -> m a
die s = liftIO $ do
  hPutStrLn stderr s
  exitFailure

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
  show s = '[' : concat (intersperse "," (map show a)) ++ " . " ++ show b ++ "]" where
    (a,b) = splitStack s

splitStack :: Stack a b -> ([a],b)
splitStack (Base b) = ([],b)
splitStack (a :. s) = (a:l,b) where
  (l,b) = splitStack s

-- Some convenient extra monad operators

infixl 1 >., >.=, >=.
infixr 1 =.<, .=<
(>.) :: Monad m => m a -> b -> m b
(>.=) :: Monad m => m a -> (a -> b) -> m b
(=.<) :: Monad m => (a -> b) -> m a -> m b
(>=.) :: Monad m => (a -> m b) -> (b -> c) -> a -> m c
(.=<) :: Monad m => (b -> c) -> (a -> m b) -> a -> m c

(>.) e r = e >> return r
(>.=) e r = e >>= return . r
(=.<) r e = return . r =<< e -- fmap, <$>, liftM
(>=.) e r = e >=> return . r
(.=<) r e = return . r <=< e

nop :: Monad m => m ()
nop = return ()

foldM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldM1 f (h:t) = foldM f h t
foldM1 _ [] = error "foldM1 applied to an empty list"

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM f (x:y) = f x >>= \b -> if b then allM f y else return False

-- The equivalents of first and second for monads (instead of arrows)
firstM :: Monad m => (a -> m b) -> (a, c) -> m (b, c)
firstM f (a,c) = f a >.= \b -> (b, c)

secondM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
secondM f (c,a) = f a >.= \b -> (c, b)

-- A monad transformer that adds Maybe failure, similar to MonadError ()

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Monad (MaybeT m) where
  m >>= f = MaybeT (runMaybeT m >>= runMaybeT . maybe nothing f)
  return = MaybeT . return . Just

instance MonadTrans MaybeT where
  lift m = MaybeT (m >.= Just)

class Monad m => MonadMaybe m where
  nothing :: m a

instance MonadPlus m => MonadMaybe m where
  nothing = mzero

instance Monad m => MonadPlus (MaybeT m) where
  mzero = MaybeT (return Nothing)
  mplus f g = MaybeT (runMaybeT f >>= maybe (runMaybeT g) (return . Just))

success :: Monad m => m ()
success = return ()

returnIf :: MonadMaybe m => a -> Bool -> m a
returnIf x True = return x
returnIf _ False = nothing

instance MonadError e m => MonadError e (MaybeT m) where
  throwError = lift . throwError
  catchError m f = MaybeT $ catchError (runMaybeT m) (runMaybeT . f)

mapMaybeT :: (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = MaybeT . f . runMaybeT

-- A monad for asynchronously interruptible computations
-- I.e., the equivalent of handle for general monads

class Monad m => MonadInterrupt m where
  handleE :: Exception e => (e -> m a) -> m a -> m a

instance MonadInterrupt IO where
  handleE = handle

instance MonadInterrupt m => MonadInterrupt (StateT s m) where
  handleE h m = get >>= \s ->
    mapStateT (handleE (\e -> runStateT (h e) s)) m

instance (MonadInterrupt m, Error e) => MonadInterrupt (ErrorT e m) where
  handleE h = mapErrorT (handleE (runErrorT . h))
