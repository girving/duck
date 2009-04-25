-- Pretty printing typeclass

module Pretty where

import Text.PrettyPrint
import qualified Data.Map as Map

class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)

  pretty = snd . pretty'
  pretty' t = (0, pretty t)

pprint :: Pretty t => t -> IO ()
pprint = print . pretty

guard :: Pretty t => Int -> t -> Doc
guard prec x
  | prec > inner = parens doc
  | otherwise = doc
  where (inner, doc) = pretty' x

instance Pretty t => Pretty [t] where
  pretty = vcat . map (guard 0)

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
