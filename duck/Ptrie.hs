{-# LANGUAGE RelaxedPolyRec #-}
-- | Duck prefix trie data structure
--
-- A prefix trie represents a partial map @[k] -> v@ with the property that no
-- key is a proper prefix of any other key.  This version additionaly maps
-- every prefix @[k] -> a@.
-- 
-- For example, a prefix trie can be used to represent the types of overloaded
-- curried functions.

module Ptrie
  ( Ptrie
  , empty
  , get
  , modify
  , lookup
  , toList
  , unionWith
  , mapInsert
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

data Ptrie k a v
  = Leaf !v
  | Node a (Map k (Ptrie k a v))
  deriving (Eq, Show)

empty :: Either a v -> Ptrie k a v
empty (Right v) = Leaf v
empty (Left a) = Node a Map.empty

get :: Ptrie k a v -> Either a v
get (Leaf v) = Right v
get (Node a _) = Left a

set :: Either a v -> Ptrie k a v -> Ptrie k a v
set (Left a) (Node _ m) = Node a m
set n _ = empty n

modify :: (Either a v -> Either a v) -> Ptrie k a v -> Ptrie k a v
modify f p = set (f (get p)) p

lookup :: Ord k => [k] -> Ptrie k a v -> Maybe (Ptrie k a v)
lookup [] t = Just t
lookup (x:k) (Node _ m) = lookup k =<< Map.lookup x m
lookup _ _ = Nothing

singleton :: Ord k => [k] -> Either a v -> Ptrie k a v
singleton [] = empty
singleton (x:k) = Node (error "Ptrie.singleton") . Map.singleton x . singleton k

insert :: Ord k => [k] -> Either a v -> Ptrie k a v -> Ptrie k a v
insert [] n p = set n p
insert (x:k) n (Node a m) = Node a $ Map.insertWith (const $ insert k n) x (singleton k n) m
insert k n _ = singleton k n

toList :: Ptrie k a v -> [([k],v)]
toList (Leaf v) = [([],v)]
toList (Node _ t) = [(x:k,v) | (x,p) <- Map.toList t, (k,v) <- toList p]

unionWith :: Ord k => (Either a v -> Either a v -> Either a v) -> Ptrie k a v -> Ptrie k a v -> Ptrie k a v
unionWith f p1 p2 = uw (f (get p1) (get p2)) p1 p2 where
  uw n (Node _ m1) (Node _ m2) = set n $ Node undefined $ Map.unionWith (unionWith f) m1 m2
  uw n p@(Node _ _) _ = set n p
  uw n _ p = set n p

mapInsert :: (Ord f, Ord k) => f -> [k] -> Either a v -> Map f (Ptrie k a v) -> Map f (Ptrie k a v)
mapInsert f k v = Map.insertWith (const $ insert k v) f (singleton k v)
