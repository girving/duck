{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
-- | Duck Operator Tree Parsing
--
-- Since the precedence of operators is adjustable, we parse expressions
-- involving operators in two passes.  This file contains the second pass.
-- Partially borrowed from <http://hackage.haskell.org/trac/haskell-prime/attachment/wiki/FixityResolution/resolve.hs>

module ParseOps
  ( Ops(..)
  , Precedence
  , Fixity(..)
  , PrecFix
  , PrecEnv
  , sortOps
  , prettyop
  ) where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

import Var
import Pretty
import SrcLoc
import ParseMonad
import Token

type Precedence = Int
type PrecFix = (Precedence, Fixity)
type PrecEnv = Map.Map Var PrecFix

data Ops a =
    OpAtom !a
  | OpUn !Var !(Ops a)
  | OpBin !Var !(Ops a) !(Ops a)
  deriving (Show)

minPrec, defaultPrec :: PrecFix
minPrec = (minBound, NonFix)
defaultPrec = (100, LeftFix)

-- This is just used for pretty printing, so we hard-code the defaults
opPrecs :: PrecEnv
opPrecs = Map.fromList [ (V v,p) | (p,vl) <-
  [((90,RightFix),  ["."])
  ,((80,RightFix),  ["^", "^^", "**"])
  ,((70,LeftFix),   ["*","/"])
  ,((60,LeftFix),   ["+","-"])
  ,((50,RightFix),  [":","++"])
  ,((40,NonFix),    ["==","!=","<","<=",">=",">"])
  ,((30,RightFix),  ["&&"])
  ,((20,RightFix),  ["||"])
  ,((10,LeftFix),   [">>",">>="])
  ,((10,RightFix),  ["<<=","$"])
  ,((2,LeftFix),    ["::"])
  ,((1,RightFix),   ["->"])
  ,((0,RightFix),   ["\\","="])
  ], v <- vl ]

opPrec :: Var -> Maybe PrecFix
opPrec op = Map.lookup op opPrecs

orderPrec :: PrecFix -> PrecFix -> Fixity
orderPrec (p1,d1) (p2,d2) = case compare p1 p2 of
    LT -> RightFix
    GT -> LeftFix
    EQ -> if d1 == d2 then d1 else NonFix

sortOps :: Show a => PrecEnv -> SrcLoc -> Ops a -> Ops a
sortOps precs loc input = out where
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
  err o = parseError loc $ "ambiguous operator expression involving" <+> quoted o

prettyop :: (Pretty f, HasVar f, Pretty a) => f -> [a] -> Doc'
prettyop f a
  | Just v <- unVar f
  , Just (i,d) <- opPrec v = case (v,a,d) of
      (V "-",[x],_)       -> i #> pf <+> x
      (_,[x,y],LeftFix)   -> i #> guard i x <+> pf <+> y
      (_,[x,y],NonFix)    -> i #> x <+> pf <+> y
      (_,[x,y],RightFix)  -> i #> x <+> pf <+> guard i y
      _ -> prettyap f a
    where pf = guard (-1) f
prettyop f a
  | Just v <- unVar f
  , Just n <- tupleLen v
  , n == length a = 3 #> punctuate ',' a
prettyop f a
  | Just (V "if") <- unVar f
  , [c,x,y] <- a = 1 #> "if" <+> pretty c <+> "then" <+> pretty x <+> "else" <+> pretty y
prettyop f a = prettyap f a

instance Pretty a => Pretty (Ops a) where
  pretty' (OpAtom a) = pretty' a
  pretty' (OpUn o a) = prettyop o [a]
  pretty' (OpBin o l r) = prettyop o [l,r]

instance Pretty PrecFix where
  pretty' (p,d) = d <+> p

instance Functor Ops where
  fmap f (OpAtom a) = OpAtom (f a)
  fmap f (OpUn v o) = OpUn v (fmap f o)
  fmap f (OpBin v o1 o2) = OpBin v (fmap f o1) (fmap f o2)

instance Fold.Foldable Ops where
  foldr f z (OpAtom a) = f a z
  foldr f z (OpUn _ r) = Fold.foldr f z r
  foldr f z (OpBin _ l r) = Fold.foldr f (Fold.foldr f z r) l

instance HasVar a => HasVar (Ops a) where
  unVar (OpAtom a) = unVar a
  unVar _ = Nothing
