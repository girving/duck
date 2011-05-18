{- Generated from "value.duck" automatically; do not edit! -}
 
{-# LINE 1 "value.duck" #-}
module Gen.Value where
{-# LINE 1 "value.duck" #-}
import Memory
{-# LINE 3 "value.duck" #-}
import Var
{-# LINE 4 "value.duck" #-}
import Type
{-# LINE 5 "value.duck" #-}
import Lir
 
{-# LINE 7 "value.duck" #-}
data FunValue = ValClosure !Var ![TypeVal] ![Value]
 
{-# LINE 7 "value.duck" #-}
instance Convert FunValue where
        {-# LINE 7 "value.duck" #-}
        value (ValClosure a b c) = valCons 0 [value a, value b, value c]
        {-# LINE 7 "value.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 8 "value.duck" #-}
                (a, b, c) = unsafeUnvalCons val
              in ValClosure (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
 
{-# LINE 15 "value.duck" #-}
data DelayValue = ValDelay !Exp ![(Var, TypedValue)]
 
{-# LINE 15 "value.duck" #-}
instance Convert DelayValue where
        {-# LINE 15 "value.duck" #-}
        value (ValDelay a b) = valCons 0 [value a, value b]
        {-# LINE 15 "value.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 16 "value.duck" #-}
                (a, b) = unsafeUnvalCons val
              in ValDelay (unsafeUnvalue a) (unsafeUnvalue b)
