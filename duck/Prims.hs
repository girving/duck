{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
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
  -- * IO primitives
  | Exit
  | IOPutChr
  | TestAll
  deriving (Eq, Ord, Show)

typeC :: IsType t => String -> t
typeC c = typeCons (V c) []

typeC1 :: IsType t => String -> t -> t
typeC1 c t = typeCons (V c) [t]

isTypeC :: String -> Type -> Bool
isTypeC c t
  | Just (V c',[]) <- unTypeCons t, c == c' = True
  | otherwise = False

isTypeC1 :: String -> Type -> Maybe Type
isTypeC1 c t
  | Just (V c',[t1]) <- unTypeCons t, c == c' = Just t1
  | otherwise = Nothing

typeUnit :: IsType t => t
typeUnit = typeC "()"

isTypeUnit :: Type -> Bool
isTypeUnit = isTypeC "()"

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

isTypeInt :: Type -> Bool
isTypeInt = isTypeC "Int"

typeChr :: IsType t => t
typeChr = typeC "Chr"

isTypeChr :: Type -> Bool
isTypeChr = isTypeC "Chr"

typeIO :: IsType t => t -> t
typeIO = typeC1 "IO"

isTypeIO :: Type -> Maybe Type
isTypeIO = isTypeC1 "IO"

typeType :: IsType t => t -> t
typeType = typeC1 "Type"

isTypeType :: Type -> Maybe Type
isTypeType = isTypeC1 "Type"

-- Pretty printing

instance Pretty Prim where
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
