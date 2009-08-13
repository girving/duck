-- | Duck Operator Tree Parsing

module ParseOps 
  ( Ops(..)
  , sortOps
  ) where

-- Since the precedence of operators is adjustable, we parse expressions
-- involving operators in two passes.  This file contains the second pass.
-- Partially borrowed from http://hackage.haskell.org/trac/haskell-prime/attachment/wiki/FixityResolution/resolve.hs

import Var
import ParseMonad
import Pretty
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

data Ops a =
    OpAtom a
  | OpUn Var (Ops a)
  | OpBin Var (Ops a) (Ops a)
  deriving (Show)

minPrec, defaultPrec :: PrecFix
minPrec = (minBound, NonFix)
defaultPrec = (100, LeftFix)

orderPrec :: PrecFix -> PrecFix -> Fixity
orderPrec (p1,d1) (p2,d2) = case compare p1 p2 of
    LT -> RightFix
    GT -> LeftFix
    EQ -> if d1 == d2 then d1 else NonFix

sortOps :: Show a => PrecEnv -> Ops a -> Ops a
sortOps precs input = out where
  (out, []) = parse minPrec Nothing toks
  parse p Nothing (Left l : rest) = 
    parse p (Just (OpAtom l)) rest
  parse p (Just l) mid@(Right (o,p') : rest) =
    case orderPrec p p' of
        NonFix -> err o
        LeftFix -> (l, mid)
        RightFix -> parse p (Just $ OpBin o l r) rest' where
          (r, rest') = parse p' Nothing rest
  parse p Nothing (Right (o,p') : rest) =
    parse p (Just (OpUn o r)) rest'
    where
      (r, rest') = parse (max p' p) Nothing rest
  parse _ (Just l) [] = (l, [])
  parse _ _ _ = error "parseOps"
  toks = map (fmap (\o -> (o, prec o))) $ otoks input []
  otoks (OpAtom a) t = Left a : t
  otoks (OpUn o r) t = Right o : otoks r t
  otoks (OpBin o l r) t = otoks l (Right o : otoks r t)
  prec o = fromMaybe defaultPrec $ Map.lookup o precs
  err o = parseThrow ("ambiguous operator expression involving " ++ (pshow o)) 

instance Pretty a => Pretty (Ops a) where
  pretty' (OpAtom a) = pretty' a
  pretty' (OpUn (V o) a) = (20, pretty o <+> pretty a)
  pretty' (OpBin (V o) l r) = (20, guard 21 l <+> pretty o <+> guard 21 r)

instance Functor Ops where
  fmap f (OpAtom a) = OpAtom (f a)
  fmap f (OpUn v o) = OpUn v (fmap f o)
  fmap f (OpBin v o1 o2) = OpBin v (fmap f o1) (fmap f o2)

instance Fold.Foldable Ops where
  foldr f z (OpAtom a) = f a z
  foldr f z (OpUn _ r) = Fold.foldr f z r
  foldr f z (OpBin _ l r) = Fold.foldr f (Fold.foldr f z r) l
