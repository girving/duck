{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleInstances, TypeSynonymInstances #-}
-- | Duck Ir Types

-- These are the same as the later Lir types in the Type module, except that Datatypes
-- are represented as Var rather than an explicit Datatype pointer.  See Lir.Type for
-- all explanations.

module IrType
  ( TypePat(..)
  , TypeFun(..)
  , typeInt, typeChar, typeArrow
  , typeSubst
  ) where

import qualified Data.Map as Map

import Pretty
import Var

data TypePat
  = TsVar Var
  | TsCons CVar [TypePat]
  | TsFun [TypeFun]
  | TsTrans Var TypePat
  | TsVoid
  deriving Show

data TypeFun
  = FunArrow TypePat TypePat
  | FunClosure Var [TypePat]
  deriving Show

typeInt :: TypePat
typeInt = TsCons (V "Int") []

typeChar :: TypePat
typeChar = TsCons (V "Char") []

typeArrow :: TypePat -> TypePat -> TypePat
typeArrow s t = TsFun [FunArrow s t]

typeSubst :: Map.Map Var TypePat -> TypePat -> TypePat
typeSubst m = ts where
  ts t@(TsVar v) = Map.findWithDefault t v m
  ts (TsCons c t) = TsCons c (map ts t)
  ts (TsFun f) = TsFun (map tf f)
  ts (TsTrans v t) = TsTrans v (ts t)
  ts TsVoid = TsVoid
  tf (FunArrow t1 t2) = FunArrow (ts t1) (ts t2)
  tf (FunClosure v t) = FunClosure v (map ts t)

-- Pretty printing

instance Pretty TypePat where
  pretty' (TsVar v) = pretty' v
  pretty' (TsCons t []) = pretty' t
  pretty' (TsCons t tl) | isTuple t = 3 #> punctuate ',' tl
  pretty' (TsCons t tl) = prettyap t tl
  pretty' (TsFun f) = pretty' f
  pretty' (TsTrans t s) = prettyap t [s]
  pretty' TsVoid = pretty' "Void"

instance Pretty TypeFun where
  pretty' (FunClosure f []) = pretty' f
  pretty' (FunClosure f tl) = prettyap f tl
  pretty' (FunArrow s t) = 1 #> s <+> "->" <+> pguard 1 t

instance Pretty [TypeFun] where
  pretty' [f] = pretty' f
  pretty' fl = 5 #> punctuate '&' fl
