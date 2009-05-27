-- Duck Operator Tree Parsing

module ParseOps 
  ( parseExpOps
  , parsePatOps
  ) where

-- Since the precedence of operators is adjustable, we parse expressions
-- involving operators in two passes.  This file contains the second pass.
-- Partially orrowed from http://hackage.haskell.org/trac/haskell-prime/attachment/wiki/FixityResolution/resolve.hs

import Var
import Ast
import ParseMonad
import Pretty

import qualified Data.Map as Map

parseOps :: (a -> Var -> a -> a) -> (Var -> a -> P a) -> [Either a Var] -> P a
parseOps binary prefix input = do
  state <- get
  let prec op = case Map.lookup op (ps_prec state) of
        Nothing -> (maxBound, Leftfix)
        Just f -> f

   -- parse :: Int -> Fixity -> [Either a Var] -> P (a, [Either a Var])
      parse _ _ [Left e] = return (e, [])
      parse p d (Left e : mid@(Right op : rest))
        | p == p' && (d /= d' || d == Nonfix) = fail ("ambiguous infix expression at operator "++show (pretty op))
        | p > p' || p == p' && (d == Leftfix || d' == Nonfix) = return (e, mid)
        | otherwise = do
          (e',rest') <- parse p' d' rest
          parse p d (Left (binary e op e') : rest')
        where (p', d') = prec op
      parse p d (Right op : rest) = do -- handle unary operators
        (e,rest') <- parse (max p' p) d rest
        e' <- prefix op e
        parse p d (Left e' : rest')
        where (p', _) = prec op
      parse _ _ _ = undefined

  (e,[]) <- parse (-1) Nonfix (reverse input)
  return e

parseExpOps :: [Either Exp Var] -> P Exp
parseExpOps = parseOps binary prefix where
  binary x op y = Apply (Var op) [x,y]
  prefix (V "-") x = return $ Apply (Var (V "negate")) [x]
  prefix op _ = fail (show (pretty op)++" cannot be used as a prefix operator (the only valid prefix operator is \"-\")")

parsePatOps :: [Either Pattern Var] -> P Pattern
parsePatOps = parseOps binary prefix where
  binary x op y = PatCons op [x,y]
  prefix = fail "unary operator in pattern" -- the parser should never let these through
