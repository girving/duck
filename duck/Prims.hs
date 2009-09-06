{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
  , binopString
  , primString
  -- * Primitive types
  , typeUnit
  , typeArrow, isTypeArrow
  , typeClosure
  , typeTuple
  , typeInt
  , typeChar
  , typeIO
  , typeType
  ) where

import Type
import Var

data Binop
  = IntAddOp
  | IntSubOp
  | IntMulOp
  | IntDivOp
  | IntEqOp
  | IntLTOp
  | IntGTOp
  | IntLEOp
  | IntGEOp
  deriving (Eq, Ord, Show)

data Prim
  = Binop Binop
  | CharIntOrd
  | IntCharChr
  -- * IO primitives
  | Exit
  | IOPutChar
  | TestAll
  deriving (Eq, Ord, Show)

typeC :: IsType t => String -> t
typeC c = typeCons (V c) []

typeC1 :: IsType t => String -> t -> t
typeC1 c t = typeCons (V c) [t]

typeUnit :: IsType t => t
typeUnit = typeC "()"

typeArrow :: IsType t => t -> t -> t
typeArrow s t = typeFun [FunArrow s t]

isTypeArrow :: TypePat -> Maybe (TypePat,TypePat)
isTypeArrow t
  | Just [FunArrow s t] <- unTypeFun t = Just (s,t)
  | otherwise = Nothing

typeClosure :: IsType t => Var -> [t] -> t
typeClosure f tl = typeFun [FunClosure f tl]

typeTuple :: IsType t => [t] -> t
typeTuple tl = typeCons (tupleCons tl) tl

typeInt :: IsType t => t
typeInt = typeC "Int"

typeChar :: IsType t => t
typeChar = typeC "Char"

typeIO :: IsType t => t -> t
typeIO = typeC1 "IO"

typeType :: IsType t => t -> t
typeType = typeC1 "Type"

-- Pretty printing


binopString :: Binop -> String
binopString op = case op of
  IntAddOp -> "+"
  IntSubOp -> "-"
  IntMulOp -> "*"
  IntDivOp -> "/"
  IntEqOp -> "=="
  IntLTOp -> "<"
  IntGTOp -> ">"
  IntLEOp -> "<="
  IntGEOp -> ">="

primString :: Prim -> String
primString (Binop op) = binopString op
primString p = show p
