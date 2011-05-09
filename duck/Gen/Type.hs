{- Generated from "type.duck" automatically; do not edit! -}
 
{-# LINE 1 "type.duck" #-}
module Gen.Type where
{-# LINE 1 "type.duck" #-}
import Memory
{-# LINE 6 "type.duck" #-}
import Var
{-# LINE 7 "type.duck" #-}
import SrcLoc
 
{-# LINE 21 "type.duck" #-}
data TypeFun t = FunArrow !Trans !t !t
               | FunClosure !Var ![t]
 
{-# LINE 21 "type.duck" #-}
instance (Convert t) => Convert (TypeFun t) where
        {-# LINE 21 "type.duck" #-}
        value (FunArrow a b c) = valCons 0 [value a, value b, value c]
        {-# LINE 21 "type.duck" #-}
        value (FunClosure a b) = valCons 1 [value a, value b]
        {-# LINE 21 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0
                  -> let {-# LINE 22 "type.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in FunArrow (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                1
                  -> let {-# LINE 23 "type.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in FunClosure (unsafeUnvalue a) (unsafeUnvalue b)
                _ -> error "bad tag in unsafeUnvalue TypeFun"
 
{-# LINE 28 "type.duck" #-}
data TypeVal = TyCons !(Box Datatype) ![TypeVal]
             | TyFun ![TypeFun TypeVal]
             | TyVoid
 
{-# LINE 28 "type.duck" #-}
instance Convert TypeVal where
        {-# LINE 28 "type.duck" #-}
        value (TyCons a b) = valCons 0 [value a, value b]
        {-# LINE 28 "type.duck" #-}
        value (TyFun a) = valCons 1 [value a]
        {-# LINE 28 "type.duck" #-}
        value (TyVoid) = valCons 2 []
        {-# LINE 28 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0
                  -> let {-# LINE 29 "type.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in TyCons (unsafeUnvalue a) (unsafeUnvalue b)
                1 -> TyFun (unsafeUnvalue (unsafeUnvalCons val))
                2 -> TyVoid
                _ -> error "bad tag in unsafeUnvalue TypeVal"
 
{-# LINE 36 "type.duck" #-}
data TypePat = TsVar !Var
             | TsCons !(Box Datatype) ![TypePat]
             | TsFun ![TypeFun TypePat]
             | TsVoid
 
{-# LINE 36 "type.duck" #-}
instance Convert TypePat where
        {-# LINE 36 "type.duck" #-}
        value (TsVar a) = valCons 0 [value a]
        {-# LINE 36 "type.duck" #-}
        value (TsCons a b) = valCons 1 [value a, value b]
        {-# LINE 36 "type.duck" #-}
        value (TsFun a) = valCons 2 [value a]
        {-# LINE 36 "type.duck" #-}
        value (TsVoid) = valCons 3 []
        {-# LINE 36 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> TsVar (unsafeUnvalue (unsafeUnvalCons val))
                1
                  -> let {-# LINE 38 "type.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in TsCons (unsafeUnvalue a) (unsafeUnvalue b)
                2 -> TsFun (unsafeUnvalue (unsafeUnvalCons val))
                3 -> TsVoid
                _ -> error "bad tag in unsafeUnvalue TypePat"
 
{-# LINE 60 "type.duck" #-}
data Variance = Covariant
              | Invariant
 
{-# LINE 60 "type.duck" #-}
instance Convert Variance where
        {-# LINE 60 "type.duck" #-}
        value (Covariant) = valCons 0 []
        {-# LINE 60 "type.duck" #-}
        value (Invariant) = valCons 1 []
        {-# LINE 60 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> Covariant
                1 -> Invariant
                _ -> error "bad tag in unsafeUnvalue Variance"
 
{-# LINE 63 "type.duck" #-}
data Trans = NoTrans
           | Delay
 
{-# LINE 63 "type.duck" #-}
instance Convert Trans where
        {-# LINE 63 "type.duck" #-}
        value (NoTrans) = valCons 0 []
        {-# LINE 63 "type.duck" #-}
        value (Delay) = valCons 1 []
        {-# LINE 63 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> NoTrans
                1 -> Delay
                _ -> error "bad tag in unsafeUnvalue Trans"
 
{-# LINE 69 "type.duck" #-}
data Datatype = Data !CVar !SrcLoc ![Var] ![Variance] !DataInfo
 
{-# LINE 69 "type.duck" #-}
instance Convert Datatype where
        {-# LINE 69 "type.duck" #-}
        value (Data a b c d e)
          = valCons 0 [value a, value b, value c, value d, value e]
        {-# LINE 69 "type.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 69 "type.duck" #-}
                (a, b, c, d, e) = unsafeUnvalCons val
              in
              Data (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                (unsafeUnvalue d)
                (unsafeUnvalue e)
 
{-# LINE 78 "type.duck" #-}
data DataInfo = DataAlgebraic ![(Loc CVar, [TypePat])]
              | DataPrim !Int
 
{-# LINE 78 "type.duck" #-}
instance Convert DataInfo where
        {-# LINE 78 "type.duck" #-}
        value (DataAlgebraic a) = valCons 0 [value a]
        {-# LINE 78 "type.duck" #-}
        value (DataPrim a) = valCons 1 [value a]
        {-# LINE 78 "type.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> DataAlgebraic (unsafeUnvalue (unsafeUnvalCons val))
                1 -> DataPrim (unsafeUnvalue (unsafeUnvalCons val))
                _ -> error "bad tag in unsafeUnvalue DataInfo"
