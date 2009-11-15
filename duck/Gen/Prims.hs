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
        value (IntAddOp) = ValCons 0 []
        {-# LINE 3 "prims.duck" #-}
        value (IntSubOp) = ValCons 1 []
        {-# LINE 3 "prims.duck" #-}
        value (IntMulOp) = ValCons 2 []
        {-# LINE 3 "prims.duck" #-}
        value (IntDivOp) = ValCons 3 []
        {-# LINE 3 "prims.duck" #-}
        value (IntEqOp) = ValCons 4 []
        {-# LINE 3 "prims.duck" #-}
        value (IntLTOp) = ValCons 5 []
        {-# LINE 3 "prims.duck" #-}
        value (IntGTOp) = ValCons 6 []
        {-# LINE 3 "prims.duck" #-}
        value (IntLEOp) = ValCons 7 []
        {-# LINE 3 "prims.duck" #-}
        value (IntGEOp) = ValCons 8 []
        {-# LINE 3 "prims.duck" #-}
        value (ChrEqOp) = ValCons 9 []
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 0 []) = IntAddOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 1 []) = IntSubOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 2 []) = IntMulOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 3 []) = IntDivOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 4 []) = IntEqOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 5 []) = IntLTOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 6 []) = IntGTOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 7 []) = IntLEOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 8 []) = IntGEOp
        {-# LINE 3 "prims.duck" #-}
        unvalue (ValCons 9 []) = ChrEqOp
        {-# LINE 3 "prims.duck" #-}
        unvalue _ = undefined
 
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
        value (Binop a) = ValCons 0 [value a]
        {-# LINE 15 "prims.duck" #-}
        value (CharIntOrd) = ValCons 1 []
        {-# LINE 15 "prims.duck" #-}
        value (IntCharChr) = ValCons 2 []
        {-# LINE 15 "prims.duck" #-}
        value (Exit) = ValCons 3 []
        {-# LINE 15 "prims.duck" #-}
        value (IOPutChar) = ValCons 4 []
        {-# LINE 15 "prims.duck" #-}
        value (TestAll) = ValCons 5 []
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 0 [a]) = Binop (unvalue a)
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 1 []) = CharIntOrd
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 2 []) = IntCharChr
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 3 []) = Exit
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 4 []) = IOPutChar
        {-# LINE 15 "prims.duck" #-}
        unvalue (ValCons 5 []) = TestAll
        {-# LINE 15 "prims.duck" #-}
        unvalue _ = undefined
