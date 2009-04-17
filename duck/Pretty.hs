-- Pretty printing typeclass

module Pretty where

import Text.PrettyPrint

class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)

  pretty = snd . pretty'
  pretty' t = (0, pretty t)

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
