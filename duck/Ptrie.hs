{-# LANGUAGE RelaxedPolyRec #-}
-- | Duck prefix trie data structure
--
-- A prefix trie represents a partial map [k] -> v with the property that no
-- key is a proper prefix of any other key.  This version additionaly maps
-- every strict prefix [k] -> a.
-- 
-- For example, a prefix trie can be used to represent the types of overloaded
-- curried functions.

module Ptrie
  ( Ptrie
  , empty
  , isEmpty
  , leaf
  , unPtrie
  , singleton
  , insert
  , mapInsert
  , lookup
  , assocs
  , toList
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

-- In order to make the representation canonical, the Maps in a Ptrie are never empty
data Ptrie k a v
  = Leaf !v
  | Node !a (Map k (Ptrie k a v))
  deriving (Eq)

-- |A very special ptrie that is an exception to the nonempty rule.
empty :: a -> Ptrie k a v
empty a = Node a Map.empty

leaf :: v -> Ptrie k a v
leaf = Leaf

isEmpty :: Ptrie k a v -> Bool
isEmpty (Node _ m) | Map.null m = True
isEmpty _ = False

unPtrie :: Ptrie k a v -> Either a v
unPtrie (Node a _) = Left a
unPtrie (Leaf v) = Right v

singleton :: [(a,k)] -> v -> Ptrie k a v
singleton [] v = Leaf v
singleton ((a,x):k) v = Node a (Map.singleton x (singleton k v))

-- |Insertion is purely destructive, both of existing prefixes of k and
-- of existing associated a values.
insert :: Ord k => [(a,k)] -> v -> Ptrie k a v -> Ptrie k a v
insert [] v _ = Leaf v
insert ((a,x):k) v (Node _ m) = Node a $ mapInsert x k v m
insert k v _ = singleton k v

mapInsert :: (Ord f, Ord k) => f -> [(a,k)] -> v -> Map f (Ptrie k a v) -> Map f (Ptrie k a v)
-- I'm so lazy
mapInsert f k v m = Map.insertWith (const $ insert k v) f (singleton k v) m

lookup :: Ord k => [k] -> Ptrie k a v -> Maybe (Ptrie k a v)
lookup [] t = Just t
lookup (_:_) (Leaf _) = Nothing
lookup (x:k) (Node _ t) = lookup k =<< Map.lookup x t

assocs :: Ord k => [k] -> Ptrie k a v -> [a]
assocs _ (Leaf _) = []
assocs [] (Node a _) = [a]
assocs (x:k) (Node a t) = a : (maybe [] (assocs k) $ Map.lookup x t)

toList :: Ptrie k a v -> [([(a,k)],v)]
toList (Leaf v) = [([],v)]
toList (Node a t) = [((a,x):k,v) | (x,p) <- Map.toList t, (k,v) <- toList p]
