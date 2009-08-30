{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
  , PrimIO(..)
  , binopString
  , binopPrecedence
  -- * Primitive types
  , typeUnit, isTypeUnit
  , typeArrow, isTypeArrow
  , typeClosure
  , typeTuple
  , typeInt, isTypeInt
  , typeChr, isTypeChr
  , typeIO, isTypeIO
  , typeType, isTypeType
  ) where

import Pretty
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
  | ChrIntOrd
  | IntChrChr
  deriving (Eq, Ord, Show)

data PrimIO
  = Exit
  | IOPutChr
  | TestAll
  deriving (Eq, Ord, Show)

typeC :: IsType t => String -> t
typeC c = typeCons (V c) []

typeC1 :: IsType t => String -> t -> t
typeC1 c t = typeCons (V c) [t]

isTypeC :: IsType t => String -> t -> Bool
isTypeC c t
  | Just (V c',[]) <- unTypeCons t, c == c' = True
  | otherwise = False

isTypeC1 :: IsType t => String -> t -> Maybe t
isTypeC1 c t
  | Just (V c',[t1]) <- unTypeCons t, c == c' = Just t1
  | otherwise = Nothing

typeUnit :: IsType t => t
typeUnit = typeC "()"

isTypeUnit :: IsType t => t -> Bool
isTypeUnit = isTypeC "()"

typeArrow :: IsType t => t -> t -> t
typeArrow s t = typeFun [FunArrow s t]

isTypeArrow :: IsType t => t -> Maybe (t,t)
isTypeArrow t
  | Just [FunArrow s t] <- unTypeFun t = Just (s,t)
  | otherwise = Nothing

typeClosure :: IsType t => Var -> [t] -> t
typeClosure f tl = typeFun [FunClosure f tl]

typeTuple :: IsType t => [t] -> t
typeTuple tl = typeCons (tupleCons tl) tl

typeInt :: IsType t => t
typeInt = typeC "Int"

isTypeInt :: IsType t => t -> Bool
isTypeInt = isTypeC "Int"

typeChr :: IsType t => t
typeChr = typeC "Chr"

isTypeChr :: IsType t => t -> Bool
isTypeChr = isTypeC "Chr"

typeIO :: IsType t => t -> t
typeIO = typeC1 "IO"

isTypeIO :: IsType t => t -> Maybe t
isTypeIO = isTypeC1 "IO"

typeType :: IsType t => t -> t
typeType = typeC1 "Type"

isTypeType :: IsType t => t -> Maybe t
isTypeType = isTypeC1 "Type"

-- Pretty printing

instance Pretty Prim where
  pretty' p = (100, pretty (show p))

instance Pretty PrimIO where
  pretty' p = (100, pretty (show p))

binopPrecedence :: Binop -> Int
binopPrecedence op = case op of
  IntAddOp -> 20
  IntSubOp -> 20
  IntMulOp -> 30
  IntDivOp -> 30
  IntEqOp -> 10
  IntLTOp -> 10
  IntLEOp -> 10
  IntGTOp -> 10
  IntGEOp -> 10

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
