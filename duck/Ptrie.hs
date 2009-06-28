-- Duck prefix trie data structure

-- A prefix trie represents a partial map [k] -> v with the property that no
-- key is a proper prefix of any other key.  For example, a prefix trie can
-- be used to represent the types of overloaded curried functions.
--
-- Prefix tries are either nonempty (Ptrie') or possibly empty (Ptrie).
-- Trailing quotes (') denote functions operating on nonempty prefix tries.

module Ptrie
  ( Ptrie
  , Ptrie'
  , empty
  , isEmpty
  , leaf
  , unleaf
  , unleaf'
  , singleton
  , singleton'
  , insert
  , insert'
  , insert''
  , lookup
  , toList
  , toList'
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

-- In order to make the representation canonical, the Maps in a Ptrie are never empty
data Ptrie' k v
  = Leaf v
  | Node (Map k (Ptrie' k v))

type Ptrie k v = Maybe (Ptrie' k v)

empty :: Ptrie k v
empty = Nothing

leaf :: v -> Ptrie k v
leaf = Just . Leaf

unleaf :: Ptrie k v -> Maybe v
unleaf = (>>= unleaf')

unleaf' :: Ptrie' k v -> Maybe v
unleaf' (Leaf v) = Just v
unleaf' _ = Nothing

isEmpty :: Ptrie k v -> Bool
isEmpty Nothing = True
isEmpty _ = False

singleton :: [k] -> v -> Ptrie k v
singleton k v = Just (singleton' k v)

singleton' :: [k] -> v -> Ptrie' k v
singleton' [] v = Leaf v
singleton' (x:k) v = Node (Map.singleton x (singleton' k v))

-- Inserting with a key k has no effect if there is an existing key which
-- is a proper prefix of k.  If insertion succeeds, all entries which contain
-- k as a prefix are clobbered.
insert :: Ord k => [k] -> v -> Ptrie k v -> Ptrie k v
insert k v t = Just (insert' k v t)

insert' :: Ord k => [k] -> v -> Ptrie k v -> Ptrie' k v
insert' k v Nothing = singleton' k v
insert' k v (Just t) = insert'' k v t

insert'' :: Ord k => [k] -> v -> Ptrie' k v -> Ptrie' k v
insert'' [] v _ = Leaf v
insert'' (_:_) _ t@(Leaf _) = t
insert'' (x:k) v (Node m) = Node (Map.alter (insert k v) x m)

lookup :: Ord k => [k] -> Ptrie k v -> Ptrie k v
lookup _ Nothing = Nothing
lookup k (Just t) = lookup' k t

lookup' :: Ord k => [k] -> Ptrie' k v -> Ptrie k v
lookup' [] t = Just t
lookup' (_:_) (Leaf _) = Nothing
lookup' (x:k) (Node t) = lookup k (Map.lookup x t)

toList :: Ptrie k v -> [([k],v)]
toList = maybe [] toList'

toList' :: Ptrie' k v -> [([k],v)]
toList' (Leaf v) = [([],v)]
toList' (Node t) = [(x:k,v) | (x,p) <- Map.toList t, (k,v) <- toList' p]
