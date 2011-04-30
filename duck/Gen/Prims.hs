{- Generated from "prims.duck" automatically; do not edit! -}
 
{-# LINE 1 "prims.duck" #-}
module Gen.Prims where
{-# LINE 1 "prims.duck" #-}
import Memory
 
{-# LINE 3 "prims.duck" #-}
data Binop = IntAddOp
           | IntSubOp
           | IntMulOp
           | IntDivOp
           | IntEqOp
           | IntLTOp
           | IntGTOp
           | IntLEOp
           | IntGEOp
           | ChrEqOp
 
{-# LINE 3 "prims.duck" #-}
instance Convert Binop where
        {-# LINE 3 "prims.duck" #-}
        value (IntAddOp) = valCons 0 []
        {-# LINE 3 "prims.duck" #-}
        value (IntSubOp) = valCons 1 []
        {-# LINE 3 "prims.duck" #-}
        value (IntMulOp) = valCons 2 []
        {-# LINE 3 "prims.duck" #-}
        value (IntDivOp) = valCons 3 []
        {-# LINE 3 "prims.duck" #-}
        value (IntEqOp) = valCons 4 []
        {-# LINE 3 "prims.duck" #-}
        value (IntLTOp) = valCons 5 []
        {-# LINE 3 "prims.duck" #-}
        value (IntGTOp) = valCons 6 []
        {-# LINE 3 "prims.duck" #-}
        value (IntLEOp) = valCons 7 []
        {-# LINE 3 "prims.duck" #-}
        value (IntGEOp) = valCons 8 []
        {-# LINE 3 "prims.duck" #-}
        value (ChrEqOp) = valCons 9 []
        {-# LINE 3 "prims.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> IntAddOp
                1 -> IntSubOp
                2 -> IntMulOp
                3 -> IntDivOp
                4 -> IntEqOp
                5 -> IntLTOp
                6 -> IntGTOp
                7 -> IntLEOp
                8 -> IntGEOp
                9 -> ChrEqOp
                _ -> error "bad tag in unsafeUnvalue Binop"
 
{-# LINE 15 "prims.duck" #-}
data Prim = Binop !Binop
          | CharIntOrd
          | IntCharChr
          | Exit
          | IOPutChar
          | TestAll
 
{-# LINE 15 "prims.duck" #-}
instance Convert Prim where
        {-# LINE 15 "prims.duck" #-}
        value (Binop a) = valCons 0 [value a]
        {-# LINE 15 "prims.duck" #-}
        value (CharIntOrd) = valCons 1 []
        {-# LINE 15 "prims.duck" #-}
        value (IntCharChr) = valCons 2 []
        {-# LINE 15 "prims.duck" #-}
        value (Exit) = valCons 3 []
        {-# LINE 15 "prims.duck" #-}
        value (IOPutChar) = valCons 4 []
        {-# LINE 15 "prims.duck" #-}
        value (TestAll) = valCons 5 []
        {-# LINE 15 "prims.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> Binop (unsafeUnvalue (unsafeUnvalCons val))
                1 -> CharIntOrd
                2 -> IntCharChr
                3 -> Exit
                4 -> IOPutChar
                5 -> TestAll
                _ -> error "bad tag in unsafeUnvalue Prim"
