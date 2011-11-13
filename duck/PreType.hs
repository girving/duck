{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-- | Duck Type precursors

module PreType
  ( module Gen.PreType
  , freePreVars
  ) where

import Var
import Type

-- Pull in definition of PreTypePat and PreDatatype
import Gen.PreType

-- |Find the set of free variables in a typeset
freePreVars :: PreTypePat -> [Var]
freePreVars (TpVar v) = [v]
freePreVars (TpCons _ tl) = concatMap freePreVars tl
freePreVars (TpFun fl) = concatMap f fl where
  f (FunArrow _ s t) = freePreVars s ++ freePreVars t
  f (FunClosure _ tl) = concatMap freePreVars tl
freePreVars TpVoid = []
