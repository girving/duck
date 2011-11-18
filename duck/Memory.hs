{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ForeignFunctionInterface #-}
-- | Duck interpreter values

-- For now, duck values are layed out in the following naive manner:
-- 
-- 1. All types are pointer sized.  In particular, there are no zero size types as yet.
-- 2. Int and Char are stored as unboxed integers.
-- 3. Algebraic datatypes are always boxed (even ()).  The first word is the tag, and
--    the remaining words are the data constructor arguments.  Even tuples have tags.

module Memory
  ( Value
  , Convert(..)
  , valCons
  , unsafeTag, UnsafeUnvalCons(..), unsafeUnvalConsN, unsafeUnvalConsNth
  , Box, unbox, box, unsafeCastBox
  , Vol, ToVol(..), readVol
  , Ref, newRef, readRef, writeRef, unsafeCastRef, unsafeFreeze
  , wordSize
  ) where

import Data.Char
import Data.Functor
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe

import Util

-- | Opaque type representing any Duck value (either boxed or unboxed)
type Value = Ptr WordPtr

-- | Runtime system functions
foreign import ccall "runtime.h duck_malloc" malloc :: WordPtr -> IO Value
foreign import ccall "runtime.h duck_print_int" debug_int :: WordPtr -> IO ()
_ignore = debug_int

wordSize :: Int
wordSize = sizeOf (undefined :: WordPtr)

valCons :: Int -> [Value] -> Value
valCons c args = unsafePerformIO $ do
  p <- malloc $ fromIntegral $ (1 + length args) * wordSize
  let c' = fromIntegral c :: WordPtr
  poke p c'
  mapM_ (\(i,a) -> pokeElemOff p i $ ptrToWordPtr a) (zip [1..] args)
  return p

unsafeTag :: Value -> Int
unsafeTag p = fromIntegral $ unsafePerformIO $ peek p

unsafeUnvalConsN :: Int -> Value -> [Value]
unsafeUnvalConsN n p = unsafePerformIO $ mapM (\i -> peekElemOff p i >.= wordPtrToPtr) [1..n]

unsafeUnvalConsNth :: Value -> Int -> Value
unsafeUnvalConsNth p n = unsafePerformIO $ peekElemOff p (succ n) >.= wordPtrToPtr

class UnsafeUnvalCons t where
  unsafeUnvalCons' :: Value -> IO t
  unsafeUnvalCons :: Value -> t
  unsafeUnvalCons p = unsafePerformIO (unsafeUnvalCons' p)

instance UnsafeUnvalCons Value where
  unsafeUnvalCons' p = peekElemOff p 1 >.= wordPtrToPtr

instance UnsafeUnvalCons (Value,Value) where
  unsafeUnvalCons' p = do
    a <- peekElemOff p 1 >.= wordPtrToPtr
    b <- peekElemOff p 2 >.= wordPtrToPtr
    return (a,b)

instance UnsafeUnvalCons (Value,Value,Value) where
  unsafeUnvalCons' p = do
    (a,b) <- unsafeUnvalCons' p
    c <- peekElemOff p 3 >.= wordPtrToPtr
    return (a,b,c)

instance UnsafeUnvalCons (Value,Value,Value,Value) where
  unsafeUnvalCons' p = do
    (a,b,c) <- unsafeUnvalCons' p
    d <- peekElemOff p 4 >.= wordPtrToPtr
    return (a,b,c,d)

instance UnsafeUnvalCons (Value,Value,Value,Value,Value) where
  unsafeUnvalCons' p = do
    (a,b,c,d) <- unsafeUnvalCons' p
    e <- peekElemOff p 5 >.= wordPtrToPtr
    return (a,b,c,d,e)

-- | Conversion between Duck and Haskell memory representations

class Convert t where
  value :: t -> Value
  unsafeUnvalue :: Value -> t

instance Convert Value where
  value = id
  unsafeUnvalue = id

instance Convert Int where
  value = intPtrToPtr . fromIntegral
  unsafeUnvalue = fromIntegral . ptrToIntPtr

instance Convert Char where
  value = value . ord
  unsafeUnvalue = chr . unsafeUnvalue

instance Convert Bool where
  value v = valCons (fromEnum v) []
  unsafeUnvalue = toEnum . unsafeTag

instance Convert a => Convert [a] where
  value [] = valCons 0 []
  value (x:l) = valCons 1 [value x,value l]
  unsafeUnvalue p = case unsafeTag p of
    0 -> []
    1 -> unsafeUnvalue x : unsafeUnvalue l where (x,l) = unsafeUnvalCons p
    _ -> error "Convert [a]"

instance Convert a => Convert (Maybe a) where
  value Nothing = valCons 0 []
  value (Just x) = valCons 1 [value x]
  unsafeUnvalue p = case unsafeTag p of
    0 -> Nothing
    1 -> Just (unsafeUnvalue x) where x = unsafeUnvalCons p
    _ -> error "Convert (Maybe a)"

instance (Convert a, Convert b) => Convert (a,b) where
  value (a,b) = valCons 0 [value a, value b]
  unsafeUnvalue p = (unsafeUnvalue a, unsafeUnvalue b) where (a,b) = unsafeUnvalCons p

instance (Convert a, Convert b, Convert c) => Convert (a,b,c) where
  value (a,b,c) = valCons 0 [value a, value b, value c]
  unsafeUnvalue p = (unsafeUnvalue a, unsafeUnvalue b, unsafeUnvalue c) where (a,b,c) = unsafeUnvalCons p

-- | Version of Value with a known corresponding Haskell type
{-
newtype KnownValue t = KnownValue (Ptr (KnownValue t))

instance Convert (KnownValue t) where
  value (KnownValue v) = castPtr v
  unsafeUnvalue = KnownValue . castPtr

unvalue :: Convert t => KnownValue t -> t
unvalue (KnownValue v) = unsafeUnvalue $ castPtr v
-}

-- | An immutable boxed cell of known type
newtype Box t = Box (Ptr (Box t))

instance Convert (Box t) where
  value (Box v) = castPtr v
  unsafeUnvalue = Box . castPtr

unbox :: Convert t => Box t -> t
unbox (Box v) = unsafeUnvalue $ unsafePerformIO $ peek $ castPtr v

box :: Convert t => t -> Box t
box v = unsafePerformIO $ do
  p <- malloc $ fromIntegral wordSize
  poke p $ ptrToWordPtr $ value v
  return $ Box $ castPtr p

-- |Cast a box to a different type
unsafeCastBox :: Box s -> Box t
unsafeCastBox (Box v) = Box $ castPtr v

-- | A mutable boxed cell of known type
newtype Ref t = Ref (Ptr (Ref t))

instance Convert (Ref t) where
  value (Ref v) = castPtr v
  unsafeUnvalue = Ref . castPtr

newRef :: Convert t => t -> IO (Ref t)
newRef v = do
  p <- malloc $ fromIntegral wordSize
  poke p $ ptrToWordPtr $ value v
  return $ Ref $ castPtr p

readRef :: Convert t => Ref t -> IO t
readRef (Ref m) = unsafeUnvalue . castPtr <$> peek (castPtr m)

writeRef :: Convert t => Ref t -> t -> IO ()
writeRef (Ref m) v = poke (castPtr m) (value v)

-- |Cast a mutable cell to a different type
unsafeCastRef :: Ref s -> IO (Ref t)
unsafeCastRef (Ref m) = return $ Ref $ castPtr m

-- |Declare a mutable cell forever frozen
unsafeFreeze :: Ref t -> IO (Box t)
unsafeFreeze (Ref m) = return $ Box $ castPtr m

-- |"Volatile" boxed cell of indeterminate mutability
newtype Vol t = Vol (Ptr (Vol t))

instance Convert (Vol t) where
  value (Vol v) = castPtr v
  unsafeUnvalue = Vol . castPtr

class ToVol b where
  toVol :: b t -> Vol t

instance ToVol Box where
  toVol (Box v) = Vol $ castPtr v

instance ToVol Ref where
  toVol (Ref m) = Vol $ castPtr m

readVol :: Convert t => Vol t -> IO t
readVol (Vol v) = unsafeUnvalue . castPtr <$> peek (castPtr v)
