{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
-- | Duck utility functions

module Util
  ( flp
  -- * IO
  , exit
  , dieWith
  , die
  , fputs
  , puts
  , debug
  , debugVal
  -- * List
  , duplicates
  , merge
  , groupPairs
  , spanJust
  , zipCheck
  , zipWithCheck
  , sameLength
  -- * Functionals
  , uncurry3
  , first, second
  , left, right
  -- * Data
  -- ** Enum
  , allOf
  , TextEnum(..)
  -- ** Stack
  , Stack(..)
  , (++.)
  , splitStack
  -- * Monad
  , nop
  , (>.), (>.=), (>=.)
  , (<<), (.<), (=.<), (.=<)
  , foldM1
  , allM
  , firstM
  , secondM
  , zipWith3M
  -- ** Maybe
  , MaybeT(..)
  , success
  , returnIf
  , mapMaybeT
  -- ** Error and Exception
  , tryError
  , MonadInterrupt(..)
  -- ** Strict Identity
  , Sequence, runSequence
  ) where

import System.IO
import System.Exit
import System.IO.Unsafe
import Data.Function
import Data.List
import Data.Maybe
import Data.Char
import Control.Exception
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans
import Foreign.C.String

flp :: (a,b) -> (b,a)
flp (a,b) = (b,a)

-- |Write a string to a stream all at once.
--
-- The string is written out all at once (as if with fputs in C), so it
-- won't end up interleaved with other strings like 'putStrLn' does.
fputs :: Handle -> String -> IO ()
fputs h s = withCStringLen s (uncurry $ hPutBuf h)

-- |Write a string to stdout with a trailing newline.
puts :: String -> IO ()
puts s = fputs stdout (s++"\n")

debug :: Show a => a -> b -> b
debug a b = unsafePerformIO (puts (show a)) `seq` b

debugVal :: Show a => a -> a
debugVal a = debug a a

-- |Find all entries that occur more than once
duplicates :: Eq a => [a] -> [a]
duplicates l = l \\ nub l

-- |Merge two unique sorted lists, eliminating duplicates.
--
-- Odd behavior will result if the lists are unsorted or contain duplicates.
-- Sorted means sorted in ascending order.
merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case compare x y of
  LT -> x : merge xs (y:ys)
  EQ -> x : merge xs ys -- left bias
  GT -> y : merge (x:xs) ys

-- Note: it'd be nice if this was linear time, or at least O(n log n)
-- See http://lambda-the-ultimate.org/node/3277
groupPairs :: Eq a => [(a,b)] -> [(a,[b])]
groupPairs pairs = map squash groups where
  squash l = (fst (head l), map snd l)
  groups = groupBy ((==) `on` fst) pairs

-- |Return the longest prefix that is Just, and the rest.
spanJust :: (a -> Maybe b) -> [a] -> ([b],[a])
spanJust _ [] = ([],[])
spanJust f l@(x:r) = maybe ([],l) (\y -> first (y:) $ spanJust f r) $ f x

-- |Same as zip, but bails if the lists aren't equal size
zipCheck :: [a] -> [b] -> Maybe [(a,b)]
zipCheck [] [] = return []
zipCheck (x:xl) (y:yl) = ((x,y) :) =.< zipCheck xl yl
zipCheck _ _ = mzero

zipWithCheck :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithCheck f x y = map (uncurry f) =.< zipCheck x y

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (a,b,c) = f a b c

zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f x y z = mapM (uncurry3 f) (zip3 x y z)

-- more efficient than Arrow instances
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

sameLength :: [a] -> [b] -> Bool
sameLength [] [] = True
sameLength (_:a) (_:b) = sameLength a b
sameLength _ _ = False

allOf :: (Enum a, Bounded a) => [a]
allOf = enumFromTo minBound maxBound

class (Eq e, Enum e, Bounded e) => TextEnum e where
  enumTexts :: [(e,String)]
  showEnum :: e -> String
  readsEnum :: String -> [(e, String)]

  enumTexts = map (\e -> (e,showEnum e)) allOf
  showEnum e = fromJust $ lookup e enumTexts
  readsEnum s =
    [ (a, drop (length t) s) 
    | (a,t) <- enumTexts
    , isPrefixOf (map toLower t) (map toLower s)
    ]

exit :: Int -> IO a
exit 0 = exitSuccess
exit i = exitWith (ExitFailure i)

dieWith :: MonadIO m => Int -> String -> m a
dieWith i s = liftIO $ do
  fputs stderr (s++"\n")
  exit i

die :: MonadIO m => String -> m a
die = dieWith 1

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
(.<) r e = e >> return r
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
  m >>= f = MaybeT $ runMaybeT m >>= maybe (return Nothing) (runMaybeT . f)
  return = MaybeT . return . Just

instance MonadTrans MaybeT where
  lift m = MaybeT (m >.= Just)

instance Monad m => MonadPlus (MaybeT m) where
  mzero = MaybeT (return Nothing)
  mplus f g = MaybeT (runMaybeT f >>= maybe (runMaybeT g) (return . Just))

success :: Monad m => m ()
success = return ()

returnIf :: MonadPlus m => a -> Bool -> m a
returnIf x True = return x
returnIf _ False = mzero

instance MonadError e m => MonadError e (MaybeT m) where
  throwError = lift . throwError
  catchError m f = MaybeT $ catchError (runMaybeT m) (runMaybeT . f)

mapMaybeT :: (m (Maybe a) -> n (Maybe b)) -> MaybeT m a -> MaybeT n b
mapMaybeT f = MaybeT . f . runMaybeT

tryError :: MonadError e m => m a -> m (Either e a)
tryError f = catchError (Right =.< f) (return . Left)

-- A monad for asynchronously interruptible computations
-- I.e., the equivalent of handle for general monads

class Monad m => MonadInterrupt m where
  handleE :: Exception e => (e -> m a) -> m a -> m a

instance MonadInterrupt IO where
  handleE = handle

instance MonadInterrupt m => MonadInterrupt (ReaderT r m) where
  handleE h m = ReaderT $ \r ->
    handleE (\e -> runReaderT (h e) r) (runReaderT m r)

instance MonadInterrupt m => MonadInterrupt (StateT s m) where
  handleE h m = StateT $ \s ->
    handleE (\e -> runStateT (h e) s) (runStateT m s)

instance (MonadInterrupt m, Error e) => MonadInterrupt (ErrorT e m) where
  handleE h = mapErrorT (handleE (runErrorT . h))

newtype Sequence a = Sequence { runSequence :: a }

instance Functor Sequence where
  fmap f = Sequence . f . runSequence

instance Monad Sequence where
  return = Sequence
  m >>= k = k $! runSequence m
  m >> k = seq (runSequence m) k
