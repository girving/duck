{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
  , PrimIO(..)
  , binopString
  , binopPrecedence
  , tyUnit
  , isTyUnit
  , tyArrow
  , tsArrow
  , isTyArrow
  , isTsArrow
  , tyClosure
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
  = ExitFailure
  | IOPutChr
  | TestAll
  deriving (Eq, Ord, Show)

-- Primitive types

tyUnit :: Type
tyUnit = TyCons (V "()") []

isTyUnit :: Type -> Bool
isTyUnit (TyCons (V "()") []) = True
isTyUnit _ = False

tyArrow :: Type -> Type -> Type
tyArrow s t = TyFun (TypeFun [(s,t)] [])

tsArrow :: TypeSet -> TypeSet -> TypeSet
tsArrow s t = TsFun (TypeFun [(s,t)] [])

isTyArrow :: Type -> Maybe (Type,Type)
isTyArrow (TyFun (TypeFun [a] [])) = Just a
isTyArrow _ = Nothing

isTsArrow :: TypeSet -> Maybe (TypeSet,TypeSet)
isTsArrow (TsFun (TypeFun [a] [])) = Just a
isTsArrow _ = Nothing

tyClosure :: Var -> [Type] -> Type
tyClosure f tl = TyFun (TypeFun [] [(f,tl)])

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
