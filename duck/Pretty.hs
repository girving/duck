{-# LANGUAGE FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
-- | Pretty printing typeclass
--
-- Mostly a class-based re-export of "Text.PrettyPrint", with a few conveniences such as precedence.
-- For precedence, we use the (extended) precedences listed at the top of base.duck, which range from 0 (always parethesized) to 110 (never); note that this is exactly 10 times the standand Haskell precedences.

module Pretty 
  ( Pretty(..)
  , Doc, Doc'
  , (#>), guard

  -- * Composition
  , (<>), (<+>), (<&>), (<&+>), ($$)
  , hcat, hsep, hcons, vcat, sep
  , punct, joinPunct, (<:>)
  , punctuate
  , nested, nestedPunct
  , parens, brackets, quoted
  , prettyap
  , sPlural

  -- * Extraction and use
  , pout, qout, poutlist
  ) where

import Text.PrettyPrint (Doc, empty, isEmpty)
import qualified Text.PrettyPrint as PP
import qualified Data.Map as Map
import Util

type PrecDoc = Int -> Doc
type Doc' = PrecDoc

appPrec :: Int
appPrec = 100

instance Show PrecDoc where
  showsPrec i p = shows (p (10*i))

-- |Things that can be converted to Doc (formatted text) representation, possibly with precedence.
class Pretty t where
  pretty :: t -> Doc
  pretty' :: t -> PrecDoc

  pretty x = pretty' x 0
  pretty' x _ = pretty x

instance Pretty Doc where
  pretty = id

instance Pretty PrecDoc where
  pretty' p i = p i


guard :: Pretty t => Int -> t -> Doc
guard = flip pretty'

prec' :: Pretty t => Int -> t -> PrecDoc
prec' i x o
  | o > i = PP.parens d
  | otherwise = d
  where d = pretty' x i

infixr 1 #>

-- |Create a representation of the given value with at least the given precedence, wrapping in parentheses as necessary.
(#>) :: Pretty t => Int -> t -> PrecDoc
(#>) i = prec' i . guard (succ i)


infixl 6 <>, <+>, <&>, <&+>
infixl 5 $$

-- these could also take into account precedence somehow

(<>) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
(<>) a b i = pretty' a i PP.<> pretty' b i

(<+>) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
(<+>) a b i = pretty' a i PP.<+> pretty' b i

-- |Just like '(<>)' except remains 'empty' if either side is empty.
(<&>) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
(<&>) a b i
  | isEmpty pa || isEmpty pb = empty
  | otherwise = pa PP.<> pb
  where
    pa = pretty' a i
    pb = pretty' b i

-- |Just like '(<+>)' except remains 'empty' if either side is empty.
(<&+>) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
(<&+>) a b i
  | isEmpty pa || isEmpty pb = empty
  | otherwise = pa PP.<+> pb
  where
    pa = pretty' a i
    pb = pretty' b i

($$) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
($$) a b i = pretty' a i PP.$$ pretty' b i

hcat :: Pretty t => [t] -> PrecDoc
hcat l i = PP.hcat $ map (guard i) l

hsep :: Pretty t => [t] -> PrecDoc
hsep l i = PP.hsep $ map (guard i) l

hcons :: (Pretty a, Pretty t) => a -> [t] -> PrecDoc
hcons h l i = PP.hsep $ guard i h : map (guard i) l

prettyap :: (Pretty a, Pretty t) => a -> [t] -> PrecDoc
prettyap h l = appPrec #> hcons h l

vcat :: Pretty t => [t] -> PrecDoc
vcat l i = PP.vcat $ map (guard i) l

sep :: Pretty t => [t] -> PrecDoc
sep l i = PP.sep $ map (guard i) l

punct :: Pretty a => Char -> a -> PrecDoc
punct c a i
  | isEmpty pa = empty
  | otherwise = pa `pc` PP.char c
  where
    pa = pretty' a i
    pc | c `elem` ":;," = (PP.<>)
       | otherwise = (PP.<+>)

withPunct :: (Pretty a, Pretty b) => (Doc -> Doc -> PrecDoc) -> Char -> a -> b -> PrecDoc
withPunct f c a b i
  | isEmpty pa = pb
  | isEmpty pb = pa
  | otherwise = f (punct c pa i) pb i
  where 
    pa = pretty' a i
    pb = pretty' b i

joinPunct :: (Pretty a, Pretty b) => Char -> a -> b -> PrecDoc
joinPunct = withPunct (<+>)

infixl 6 <:>

(<:>) :: (Pretty a, Pretty b) => a -> b -> PrecDoc
(<:>) = joinPunct ':'

nested :: (Pretty a, Pretty b) => a -> b -> PrecDoc
nested a b i
  | isEmpty pb = pa
  | isEmpty pa = pb
  | otherwise = PP.hang pa 2 pb
  where 
    pa = pretty' a i
    pb = pretty' b i

nestedPunct :: (Pretty a, Pretty b) => Char -> a -> b -> PrecDoc
nestedPunct = withPunct nested

punctuate :: Pretty t => Char -> [t] -> PrecDoc
punctuate _ [] = const empty
punctuate _ [x] = pretty' x
punctuate d (x:l) = punct d x <+> punctuate d l

grouped :: Pretty t => (Doc -> Doc) -> t -> Doc
grouped f x = f $ pretty x

quoted :: Pretty t => t -> Doc
quoted = grouped PP.quotes

parens :: Pretty t => t -> Doc
parens = grouped PP.parens

brackets :: Pretty t => t -> Doc
brackets = grouped PP.brackets

sPlural :: [a] -> Doc
sPlural [_] = empty
sPlural _ = PP.char 's'


class PrettyOut o where
  pout :: Pretty t => t -> o

instance PrettyOut Doc where
  pout = pretty

instance PrettyOut PrecDoc where
  pout = pretty'

instance PrettyOut String where
  pout = PP.render . pretty

instance PrettyOut ShowS where
  pout = shows . pretty

instance PrettyOut (IO ()) where
  pout = puts . pout

qout :: (Pretty t, PrettyOut o) => t -> o
qout = pout . quoted

poutlist :: (Pretty t, PrettyOut o) => [t] -> o
poutlist = pout . hsep


instance Pretty () where
  pretty () = empty

instance Pretty Int where
  pretty = PP.int

instance Pretty Char where
  pretty = PP.char

instance Pretty String where
  pretty "" = empty
  pretty s = PP.text s

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pretty' = vcat . map (uncurry $ nestedPunct '=') . Map.toList
