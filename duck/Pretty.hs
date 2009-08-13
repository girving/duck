{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}
-- | Pretty printing typeclass

module Pretty 
  ( Pretty(..)
  , pprint
  , pshow
  , guard
  , vjoin

  , Doc
  , (<>), (<+>), ($$)
  , hcat, hsep, vcat, sep
  , nest
  , equals
  , parens, brackets
  ) where

import Text.PrettyPrint
import qualified Data.Map as Map

class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)
  prettylist :: [t] -> Doc

  pretty = snd . pretty'
  pretty' t = (0, pretty t)
  prettylist = hsep . map (guard 99)

pprint :: Pretty t => t -> IO ()
pprint = print . pretty

pshow :: Pretty t => t -> String
pshow = render . pretty

guard :: Pretty t => Int -> t -> Doc
guard prec x
  | prec > inner = parens doc
  | otherwise = doc
  where (inner, doc) = pretty' x

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

vjoin :: Char -> [Doc] -> Doc
vjoin _ [] = empty
vjoin sep (x:rest) = vcat ((space <+> x) : map (char sep <+>) rest)
