{-# LANGUAGE PatternGuards, StandaloneDeriving #-}
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
  , datatypeDelay
  , datatypeType
  , datatypeBool
  -- * Primitive types
  , typeUnit
  , typeArrow, isTypeArrow
  , typeClosure
  , typeTuple
  , typeInt
  , typeChar
  , typeType
  , typeBool
  , transType
  ) where

import Type
import Var
import SrcLoc
import Memory

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
  dt i = makeDatatype c noLoc vars (replicate i Covariant) $ DataAlgebraic [(L noLoc c, map TsVar vars)] where
    c = tupleCons vars
    vars = take i standardVars

datatypeUnit = makeDatatype (V "()") noLoc [] [] $ DataAlgebraic [(L noLoc (V "()"), [])]
datatypeInt = makeDatatype (V "Int") noLoc [] [] $ DataPrim wordSize -- TODO: change size?
datatypeChar = makeDatatype (V "Char") noLoc [] [] $ DataPrim wordSize -- TODO: change size
datatypeDelay = makeDatatype (V "Delay") noLoc [V "a"] [Covariant] $ DataPrim wordSize
datatypeType = makeDatatype (V "Type") noLoc [V "t"] [Invariant] $ DataPrim 0
datatypeBool = makeDatatype (V "Bool") noLoc [] [] $ DataAlgebraic [(L noLoc (V "False"),[]),
                                                                    (L noLoc (V "True") ,[])]

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
typeArrow s t = typeFun [FunArrow NoTrans s t]

isTypeArrow :: TypePat -> Maybe (TypePat,TypePat)
isTypeArrow t
  | Just [FunArrow NoTrans s t] <- unTypeFun t = Just (s,t)
  | otherwise = Nothing

typeClosure :: IsType t => Var -> [t] -> t
typeClosure f tl = typeFun [FunClosure f tl]

typeTuple :: IsType t => [t] -> t
typeTuple tl = typeCons (datatypeTuples !! length tl) tl

typeInt :: IsType t => t
typeInt = typeC datatypeInt

typeChar :: IsType t => t
typeChar = typeC datatypeChar

typeType :: IsType t => t -> t
typeType = typeC1 datatypeType

typeBool :: IsType t => t
typeBool = typeC datatypeBool

-- |Converts an annotation argument type to the effective type of the argument within the function.
transType :: IsType t => TransType t -> t
transType (NoTrans, t) = t
transType (Delay, t) = typeCons datatypeDelay [t]
transType (Static, t) = t -- really TyStatic


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
