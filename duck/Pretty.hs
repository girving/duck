{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}
-- | Pretty printing typeclass

module Pretty 
  ( Pretty(..)
  , pprint
  , pshow
  , pshowlist
  , qshow
  , guard
  , mapPretty

  , Doc
  , (<>), (<+>), ($$)
  , hcat, hsep, vcat, sep
  , nest
  , nested, nested'
  , equals
  , parens, brackets, quotes
  ) where

import Text.PrettyPrint
import qualified Data.Map as Map
import Util

class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)
  prettylist :: [t] -> Doc

  pretty = snd . pretty'
  pretty' t = (0, pretty t)
  prettylist = hsep . map (guard 99)

pprint :: Pretty t => t -> IO ()
pprint = puts . pshow

pshow :: Pretty t => t -> String
pshow = render . pretty

qshow :: Pretty t => t -> String
qshow = render . quotes . pretty

pshowlist :: Pretty t => [t] -> String
pshowlist = render . prettylist

guard :: Pretty t => Int -> t -> Doc
guard prec x
  | prec > inner = parens doc
  | otherwise = doc
  where (inner, doc) = pretty' x

instance Pretty Doc where
  pretty = id

instance Pretty t => Pretty [t] where
  pretty = vcat . map pretty

instance (Pretty s, Pretty t) => Pretty (s,t) where
  pretty (s,t) = pretty s $$ pretty t

instance Pretty () where
  pretty' () = (100, empty)

instance Pretty Int where
  pretty' i = (100, int i)

instance Pretty Char where
  pretty' c = (100, char c)

instance Pretty [Char] where
  pretty' s = (100, text s)

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pretty = Map.foldWithKey (\k v s ->
    s $$ pretty k <+> equals <+> pretty v) empty

mapPretty :: Pretty a => (Doc -> Doc) -> a -> Doc
mapPretty f a
  | isEmpty a' = empty
  | otherwise = f a'
  where a' = pretty a

nested :: (Pretty a, Pretty b) => a -> b -> Doc
nested a b
  | isEmpty b' = a'
  | isEmpty a' = b'
  | otherwise = hang a' 2 b'
  where 
    a' = pretty a
    b' = pretty b

nested' :: (Pretty a, Pretty b) => a -> b -> Doc
nested' = nested . mapPretty (<> colon)
