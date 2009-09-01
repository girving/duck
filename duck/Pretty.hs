{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}
-- | Pretty printing typeclass
--
-- Mostly a re-export of "Text.PrettyPrint", with a few conveniences such as precedence.

module Pretty 
  ( Pretty(..)
  , Doc
  , guard
  -- * Convenience functions
  , pprint
  , pshow
  , pshowlist
  , qshow

  -- * Operators
  , (<>), (<+>), (<?>), (<?+>), ($$)
  , hcat, hsep, vcat, sep
  , punct, sepPunct, (<:+>)
  , nested, nestedPunct
  , PP.equals -- probably eliminable
  , parens, brackets, quoted
  , punctuate
  ) where

import Text.PrettyPrint (Doc, empty, isEmpty)
import qualified Text.PrettyPrint as PP
import qualified Data.Map as Map
import Util

-- It may be cleaner to use showsPrec-type precedence

class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> (Int, Doc)
  prettylist :: [t] -> Doc

  pretty = snd . pretty'
  pretty' t = (0, pretty t)
  prettylist = hsep . map (guard 99)

guard :: Pretty t => Int -> t -> Doc
guard prec x
  | prec > inner = PP.parens doc
  | otherwise = doc
  where (inner, doc) = pretty' x

instance Pretty Doc where
  pretty = id

instance Pretty () where
  pretty' () = (100, empty)

instance Pretty Int where
  pretty' i = (100, PP.int i)

instance Pretty Char where
  pretty' c = (100, PP.char c)

instance Pretty [Char] where
  pretty' "" = (100, empty)
  pretty' s = (100, PP.text s)

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pretty = PP.vcat . map (uncurry $ nestedPunct '=') . Map.toList

newtype PrecDoc = PrecDoc (Int,Doc)

instance Pretty PrecDoc where
  pretty' (PrecDoc pd) = pd


infixl 6 <>, <+>, <?>, <?+>, <:+>
infixl 5 $$

-- these could also take into account precedence somehow

(<>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <> b = pretty a PP.<> pretty b

(<+>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <+> b = pretty a PP.<+> pretty b

-- |Just like '(<>)' except remains 'empty' if either side is empty.
(<?>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <?> b
  | isEmpty pa || isEmpty pb = empty
  | otherwise = pa PP.<> pb
  where
    pa = pretty a
    pb = pretty b

-- |Just like '(<+>)' except remains 'empty' if either side is empty.
(<?+>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <?+> b
  | isEmpty pa || isEmpty pb = empty
  | otherwise = pa PP.<+> pb
  where
    pa = pretty a
    pb = pretty b

($$) :: (Pretty a, Pretty b) => a -> b -> Doc
a $$ b = pretty a PP.$$ pretty b

hcat :: Pretty t => [t] -> Doc
hcat = PP.hcat . map pretty

hsep :: Pretty t => [t] -> Doc
hsep = PP.hsep . map pretty

vcat :: Pretty t => [t] -> Doc
vcat = PP.vcat . map pretty

sep :: Pretty t => [t] -> Doc
sep = PP.sep . map pretty

pprint :: Pretty t => t -> IO ()
pprint = puts . pshow

pshow :: Pretty t => t -> String
pshow = PP.render . pretty

qshow :: Pretty t => t -> String
qshow = PP.render . PP.quotes . pretty

pshowlist :: Pretty t => [t] -> String
pshowlist = PP.render . prettylist

punct :: Pretty a => Char -> a -> Doc
punct c a
  | isEmpty pa = empty
  | otherwise = pretty a `pc` PP.char c
  where
    pa = pretty a
    pc | c `elem` ":;," = (<>)
       | otherwise = (<+>)

withPunct :: (Pretty a, Pretty b) => (Doc -> Doc -> Doc) -> Char -> a -> b -> Doc
withPunct f c a b
  | isEmpty pa = pb
  | isEmpty pb = pa
  | otherwise = punct c pa `f` pb
  where 
    pa = pretty a
    pb = pretty b

sepPunct :: (Pretty a, Pretty b) => Char -> a -> b -> Doc
sepPunct = withPunct (<+>)

(<:+>) :: (Pretty a, Pretty b) => a -> b -> Doc
(<:+>) = sepPunct ':'

nested :: (Pretty a, Pretty b) => a -> b -> Doc
nested a b
  | isEmpty pb = pa
  | isEmpty pa = pb
  | otherwise = PP.hang pa 2 pb
  where 
    pa = pretty a
    pb = pretty b

nestedPunct :: (Pretty a, Pretty b) => Char -> a -> b -> Doc
nestedPunct = withPunct nested

punctuate :: (Pretty d, Pretty t) => d -> [t] -> Doc
punctuate d = sep . PP.punctuate (pretty d) . map pretty

grouped :: Pretty t => (Doc -> Doc) -> t -> PrecDoc
grouped f t = PrecDoc (100,f (pretty t))

quoted :: Pretty t => t -> PrecDoc
quoted = grouped PP.quotes

parens :: Pretty t => t -> PrecDoc
parens = grouped PP.parens

brackets :: Pretty t => t -> PrecDoc
brackets = grouped PP.brackets
