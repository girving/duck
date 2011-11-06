{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-- | Duck Type precursors

module PreType
  ( PreTypePat(..)
  , PreDatatype(..)
  , PreDataInfo(..)
  , freeVars
  ) where

import Var
import Type hiding (freeVars)

-- Pull in definition of PreTypePat and PreDatatype
import Gen.PreType

-- |Find the set of free variables in a typeset
freeVars :: PreTypePat -> [Var]
freeVars (TpVar v) = [v]
freeVars (TpCons _ tl) = concatMap freeVars tl
freeVars (TpFun fl) = concatMap f fl where
  f (FunArrow _ s t) = freeVars s ++ freeVars t
  f (FunClosure _ tl) = concatMap freeVars tl
freeVars TpVoid = []
