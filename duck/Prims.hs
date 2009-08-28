{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operation declarations

module Prims 
  ( Binop(..)
  , Prim(..)
  , PrimIO(..)
  , binopString
  , binopPrecedence
  -- * Primitive types
  , tyUnit
  , tsUnit
  , isTyUnit
  , tyArrow
  , tsArrow
  , isTyArrow
  , isTsArrow
  , tyClosure
  , tyInt
  , tsInt
  , isTyInt
  , tyChr
  , tsChr
  , isTyChr
  , tyIO
  , tsIO
  , isTyIO
  , tyType
  , isTyType
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

tyUnit :: Type
tyUnit = TyCons (V "()") []
tsUnit = singleton tyUnit

isTyUnit :: Type -> Bool
isTyUnit (TyCons (V "()") []) = True
isTyUnit _ = False

tyArrow :: Type -> Type -> Type
tyArrow s t = TyFun (TypeFun [(s,t)] [])

tsArrow :: TypePat -> TypePat -> TypePat
tsArrow s t = TsFun (TypeFun [(s,t)] [])

isTyArrow :: Type -> Maybe (Type,Type)
isTyArrow (TyFun (TypeFun [a] [])) = Just a
isTyArrow _ = Nothing

isTsArrow :: TypePat -> Maybe (TypePat,TypePat)
isTsArrow (TsFun (TypeFun [a] [])) = Just a
isTsArrow _ = Nothing

tyClosure :: Var -> [Type] -> Type
tyClosure f tl = TyFun (TypeFun [] [(f,tl)])

tyInt :: Type
tyInt = TyCons (V "Int") []
tsInt = singleton tyInt

isTyInt :: Type -> Bool
isTyInt (TyCons (V "Int") []) = True
isTyInt _ = False

tyChr :: Type
tyChr = TyCons (V "Chr") []
tsChr = singleton tyChr

isTyChr :: Type -> Bool
isTyChr (TyCons (V "Chr") []) = True
isTyChr _ = False

tyIO :: Type -> Type
tyIO t = TyCons (V "IO") [t]

tsIO :: TypePat -> TypePat
tsIO t = TsCons (V "IO") [t]

isTyIO :: Type -> Maybe Type
isTyIO (TyCons (V "IO") [t]) = Just t
isTyIO _ = Nothing

tyType :: Type -> Type
tyType t = TyCons (V "Type") [t]

isTyType :: Type -> Maybe Type
isTyType (TyCons (V "Type") [t]) = Just t
isTyType _ = Nothing

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
