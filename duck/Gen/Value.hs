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
{-# LINE 6 "value.duck" #-}
import Prims
 
{-# LINE 13 "value.duck" #-}
data FunValue = ValClosure !Var ![TypeVal] ![Value]
 
{-# LINE 13 "value.duck" #-}
instance Convert FunValue where
        {-# LINE 13 "value.duck" #-}
        value (ValClosure a b c) = valCons 0 [value a, value b, value c]
        {-# LINE 13 "value.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 14 "value.duck" #-}
                (a, b, c) = unsafeUnvalCons val
              in ValClosure (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
 
{-# LINE 16 "value.duck" #-}
data DelayValue = ValDelay !Exp ![(Var, TypeVal, Value)]
 
{-# LINE 16 "value.duck" #-}
instance Convert DelayValue where
        {-# LINE 16 "value.duck" #-}
        value (ValDelay a b) = valCons 0 [value a, value b]
        {-# LINE 16 "value.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 17 "value.duck" #-}
                (a, b) = unsafeUnvalCons val
              in ValDelay (unsafeUnvalue a) (unsafeUnvalue b)
 
{-# LINE 20 "value.duck" #-}
data IOValue = ValLiftIO !Value
             | ValPrimIO !Prim ![Value]
             | ValBindIO !Var !TypeVal !IOValue !Exp ![(Var, TypeVal, Value)]
 
{-# LINE 20 "value.duck" #-}
instance Convert IOValue where
        {-# LINE 20 "value.duck" #-}
        value (ValLiftIO a) = valCons 0 [value a]
        {-# LINE 20 "value.duck" #-}
        value (ValPrimIO a b) = valCons 1 [value a, value b]
        {-# LINE 20 "value.duck" #-}
        value (ValBindIO a b c d e)
          = valCons 2 [value a, value b, value c, value d, value e]
        {-# LINE 20 "value.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> ValLiftIO (unsafeUnvalue (unsafeUnvalCons val))
                1
                  -> let {-# LINE 22 "value.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ValPrimIO (unsafeUnvalue a) (unsafeUnvalue b)
                2
                  -> let {-# LINE 23 "value.duck" #-}
                         (a, b, c, d, e) = unsafeUnvalCons val
                       in
                       ValBindIO (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                         (unsafeUnvalue d)
                         (unsafeUnvalue e)
                _ -> error "bad tag in unsafeUnvalue IOValue"
