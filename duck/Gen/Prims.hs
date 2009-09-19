{- Generated from "prims.duck" automatically; do not edit! -}
 
{-# LINE 1 "prims.duck" #-}
module Gen.Prims where
 
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
 
{-# LINE 15 "prims.duck" #-}
data Prim = Binop !Binop
          | CharIntOrd
          | IntCharChr
          | Exit
          | IOPutChar
          | TestAll
