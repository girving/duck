-- | Source file location annotations for reporting

module SrcLoc
  ( SrcLoc(srcCol)
  , srcFile
  , before
  , startLoc
  , incrLoc
  , sameLine
  , noLoc
  , hasLoc
  , Loc(..)
  ) where

import Data.Monoid
import Pretty

data SrcLoc 
  = SrcNone
    { srcFile :: String }
  | SrcLoc 
    { srcFile :: String
    , srcLine, srcCol :: !Int
    }
  | SrcRng
    { srcFile :: String
    , srcLine, srcCol :: !Int
    , _srcEndLine, _srcEndCol :: !Int
    }

data Loc a = Loc { srcLoc :: SrcLoc, unLoc :: a }

instance Functor Loc where
  fmap f (Loc l x) = Loc l (f x)

instance Show SrcLoc where
  show (SrcNone "") = "<unknown>"
  show (SrcNone s) = s
  show (SrcLoc file line col) = file ++ ':' : shows line (':' : show col)
  show (SrcRng file line col line' col')
    | line == line' = file ++ ':' : shows line (':' : shows col ('-' : show col'))
    | otherwise = file ++ ':' : shows line (':' : shows col ('-' : shows line' (':' : show col')))

-- By default, locations drop away when printing
instance Show t => Show (Loc t) where
  show (Loc _ x) = show x

instance Pretty t => Pretty (Loc t) where
  pretty' (Loc _ x) = pretty' x

-- |The location immediately before another
before :: SrcLoc -> SrcLoc
before l@(SrcNone _) = l
before (SrcLoc f l c) = SrcLoc f l (c-1)
before (SrcRng f l c _ _) = SrcLoc f l (c-1)

startLoc :: String -> SrcLoc
startLoc file = SrcLoc file 1 1

incrLoc :: SrcLoc -> Char -> SrcLoc
incrLoc l@(SrcNone _) _ = l
incrLoc l '\n' = l{ srcLine = succ $ srcLine l, srcCol = 1 }
incrLoc l _    = l{ srcCol = succ $ srcCol l }

sameLine :: SrcLoc -> SrcLoc -> Bool
sameLine s t = srcLine s == srcLine t

joinFile :: String -> String -> String
joinFile "" s = s
joinFile s _ = s {- this is probably too slow to be worth it:
joinFile s "" = s
joinFile s1 s2 = s1
  | s1 == s2 = s1
  | otherwise = s1 ++ ';' : s2 -}

joinLocs :: SrcLoc -> String -> Int -> Int -> SrcLoc
joinLocs (SrcNone s1) s2 r2 c2 = SrcLoc (joinFile s1 s2) r2 c2
joinLocs l s2 r2 c2 
  | srcLine l == r2 && srcCol l == c2 = SrcLoc s r2 c2
  | otherwise = SrcRng s (srcLine l) (srcCol l) r2 c2
  where s = joinFile (srcFile l) s2

instance Monoid SrcLoc where
  mempty = SrcNone ""

  mappend (SrcNone s) l = l{ srcFile = joinFile s (srcFile l) }
  mappend l (SrcNone s) = l{ srcFile = joinFile (srcFile l) s }
  mappend l (SrcLoc s2 r2 c2) = joinLocs l s2 r2 c2
  mappend l (SrcRng s2 _ _ r2 c2) = joinLocs l s2 r2 c2

noLoc :: SrcLoc
noLoc = mempty

hasLoc :: SrcLoc -> Bool
hasLoc (SrcNone "") = False
hasLoc _ = True

{-
srcRng :: SrcLoc -> SrcLoc -> SrcLoc
srcRng = mappend

srcLocStart :: SrcLoc -> SrcLoc
srcLocStart (SrcRng s r c _ _) = SrcLoc s r c
srcLocStart l = l

srcLocEnd :: SrcLoc -> SrcLoc
srcLocEnd (SrcRng s _ _ r c) = SrcLoc s r c
srcLocEnd l = l
-}
