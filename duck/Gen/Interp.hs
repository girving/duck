{- Generated from "interp.duck" automatically; do not edit! -}
 
{-# LINE 1 "interp.duck" #-}
module Gen.Interp where
{-# LINE 1 "interp.duck" #-}
import Memory
{-# LINE 1 "interp.duck" #-}
import Var
{-# LINE 2 "interp.duck" #-}
import Type
{-# LINE 3 "interp.duck" #-}
import Lir
 
{-# LINE 10 "interp.duck" #-}
data DelayValue = ValDelay !Exp ![(Var, Any)]
 
{-# LINE 10 "interp.duck" #-}
instance Convert DelayValue where
        {-# LINE 10 "interp.duck" #-}
        value (ValDelay a b) = valCons 0 [value a, value b]
        {-# LINE 10 "interp.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 11 "interp.duck" #-}
                (a, b) = unsafeUnvalCons val
              in ValDelay (unsafeUnvalue a) (unsafeUnvalue b)
