{-# LANGUAGE PatternGuards, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
  , binopString
  , primString
  -- * Primitive datatypes
  , datatypeUnit
  , datatypeTuples
  , isDatatypeTuple
  , datatypeInt
  , datatypeChar
  , datatypeIO
  , datatypeDelayed
  , datatypeType
  , datatypeBool
  -- * Primitive types
  , typeUnit
  , typeArrow, isTypeArrow
  , typeClosure
  , typeTuple
  , typeInt
  , typeChar
  , typeIO
  , typeType
  , typeBool
  ) where

import Type
import Var
import SrcLoc

-- Pull in definitions of Binop and Prim
import Gen.Prims

-- Add instance declarations
deriving instance Eq Binop
deriving instance Ord Binop
deriving instance Show Binop
deriving instance Eq Prim
deriving instance Ord Prim
deriving instance Show Prim

-- |Primitive datatypes

datatypeTuples = datatypeUnit : error "no singleton tuples" : map dt [2..] where
  dt i = makeDatatype c noLoc vars [(L noLoc c, map TsVar vars)] (replicate i Covariant) where
    c = tupleCons vars
    vars = take i standardVars

datatypeInt = makeDatatype (V "Int") noLoc [] [] []
datatypeChar = makeDatatype (V "Char") noLoc [] [] []
datatypeIO = makeDatatype (V "IO") noLoc [V "a"] [] [Covariant]
datatypeDelayed = makeDatatype (V "Delayed") noLoc [V "a"] [] [Covariant]
datatypeType = makeDatatype (V "Type") noLoc [V "t"] [] [Invariant]
datatypeBool = makeDatatype (V "Bool") noLoc [] [(L noLoc (V "False"),[]),
                                                 (L noLoc (V "True") ,[])] []

isDatatypeTuple :: Datatype -> Bool
isDatatypeTuple = isTuple . dataName

-- Type construction convenience functions

typeC :: IsType t => Datatype -> t
typeC c = typeCons c []

typeC1 :: IsType t => Datatype -> t -> t
typeC1 c t = typeCons c [t]

typeUnit :: IsType t => t
typeUnit = typeC datatypeUnit

typeArrow :: IsType t => t -> t -> t
typeArrow s t = typeFun [FunArrow s t]

isTypeArrow :: TypePat -> Maybe (TypePat,TypePat)
isTypeArrow t
  | Just [FunArrow s t] <- unTypeFun t = Just (s,t)
  | otherwise = Nothing

typeClosure :: IsType t => Var -> [t] -> t
typeClosure f tl = typeFun [FunClosure f tl]

typeTuple :: IsType t => [t] -> t
typeTuple tl = typeCons (datatypeTuples !! length tl) tl

typeInt :: IsType t => t
typeInt = typeC datatypeInt

typeChar :: IsType t => t
typeChar = typeC datatypeChar

typeIO :: IsType t => t -> t
typeIO = typeC1 datatypeIO

typeType :: IsType t => t -> t
typeType = typeC1 datatypeType

typeBool :: IsType t => t
typeBool = typeC datatypeBool

-- Pretty printing


binopString :: Binop -> String
binopString op = case op of
  IntAddOp -> "+"
  IntSubOp -> "-"
  IntMulOp -> "*"
  IntDivOp -> "/"
  IntEqOp -> "=="
  ChrEqOp -> "=="
  IntLTOp -> "<"
  IntGTOp -> ">"
  IntLEOp -> "<="
  IntGEOp -> ">="

primString :: Prim -> String
primString (Binop op) = binopString op
primString p = show p
