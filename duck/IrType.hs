{-# LANGUAGE PatternGuards, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, FlexibleInstances, TypeSynonymInstances, StandaloneDeriving #-}
-- | Duck Ir Types

-- These are the same as the later Lir types in the Type module, except that Datatypes
-- are represented as Var rather than an explicit Datatype pointer.  See Lir.Type for
-- all explanations.

module IrType
  ( TypePat(..)
  , TypeFun(..)
  , typeInt, typeChar, typeArrow
  ) where

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
  pretty' (FunArrow s t) = 1 #> s <+> "->" <+> guard 1 t

instance Pretty [TypeFun] where
  pretty' [f] = pretty' f
  pretty' fl = 5 #> punctuate '&' fl
