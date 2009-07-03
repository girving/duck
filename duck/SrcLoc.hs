module SrcLoc
  ( SrcLoc
  , srcFile
  , startLoc
  , moveLoc
  ) where

import Data.Monoid

data SrcLoc = SrcLoc 
  { srcFile :: String
  , srcLine, srcCol :: !Int
  }

instance Show SrcLoc where
  show (SrcLoc "" 0 0) = "<unknown>"
  show (SrcLoc file line col) = file ++ ':' : show line ++ ':' : show col

startLoc :: String -> SrcLoc
startLoc file = SrcLoc file 1 1

moveLoc :: SrcLoc -> Char -> SrcLoc
moveLoc l '\n' = l{ srcLine = succ $ srcLine l, srcCol = 1 }
moveLoc l _    = l{ srcCol = succ $ srcCol l }

instance Monoid SrcLoc where
  mempty = SrcLoc "" 0 0

  mappend (SrcLoc "" 0 0) l = l
  mappend l _ = l
