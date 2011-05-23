{- Generated from "value.duck" automatically; do not edit! -}
 
{-# LINE 1 "value.duck" #-}
module Gen.Value where
{-# LINE 1 "value.duck" #-}
import Memory
{-# LINE 3 "value.duck" #-}
import Var
{-# LINE 4 "value.duck" #-}
import Type
 
{-# LINE 6 "value.duck" #-}
data FunValue = ValClosure !Var ![TypeVal] ![Value]
 
{-# LINE 6 "value.duck" #-}
instance Convert FunValue where
        {-# LINE 6 "value.duck" #-}
        value (ValClosure a b c) = valCons 0 [value a, value b, value c]
        {-# LINE 6 "value.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 7 "value.duck" #-}
                (a, b, c) = unsafeUnvalCons val
              in ValClosure (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
