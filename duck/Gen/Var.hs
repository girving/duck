{- Generated from "var.duck" automatically; do not edit! -}
 
{-# LINE 1 "var.duck" #-}
module Gen.Var where
{-# LINE 1 "var.duck" #-}
import Memory
 
{-# LINE 3 "var.duck" #-}
newtype Var = V [Char]
 
{-# LINE 3 "var.duck" #-}
instance Convert Var where
        {-# LINE 3 "var.duck" #-}
        value (V a) = valCons 0 [value a]
        {-# LINE 3 "var.duck" #-}
        unsafeUnvalue val = V (unsafeUnvalue (unsafeUnvalCons val))
