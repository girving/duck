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
{-# LINE 7 "value.duck" #-}
import Memory
 
{-# LINE 14 "value.duck" #-}
data FunValue = ValClosure !Var ![TypeVal] ![Value]
              | ValDelay !Exp ![(Var, TypeVal, Value)]
 
{-# LINE 14 "value.duck" #-}
instance Convert FunValue where
        {-# LINE 14 "value.duck" #-}
        value (ValClosure a b c) = ValCons 0 [value a, value b, value c]
        {-# LINE 14 "value.duck" #-}
        value (ValDelay a b) = ValCons 1 [value a, value b]
        {-# LINE 14 "value.duck" #-}
        unvalue (ValCons 0 [a, b, c])
          = ValClosure (unvalue a) (unvalue b) (unvalue c)
        {-# LINE 14 "value.duck" #-}
        unvalue (ValCons 1 [a, b]) = ValDelay (unvalue a) (unvalue b)
        {-# LINE 14 "value.duck" #-}
        unvalue _ = undefined
 
{-# LINE 19 "value.duck" #-}
data IOValue = ValLiftIO !Value
             | ValPrimIO !Prim ![Value]
             | ValBindIO !Var !TypeVal !IOValue !Exp ![(Var, TypeVal, Value)]
 
{-# LINE 19 "value.duck" #-}
instance Convert IOValue where
        {-# LINE 19 "value.duck" #-}
        value (ValLiftIO a) = ValCons 0 [value a]
        {-# LINE 19 "value.duck" #-}
        value (ValPrimIO a b) = ValCons 1 [value a, value b]
        {-# LINE 19 "value.duck" #-}
        value (ValBindIO a b c d e)
          = ValCons 2 [value a, value b, value c, value d, value e]
        {-# LINE 19 "value.duck" #-}
        unvalue (ValCons 0 [a]) = ValLiftIO (unvalue a)
        {-# LINE 19 "value.duck" #-}
        unvalue (ValCons 1 [a, b]) = ValPrimIO (unvalue a) (unvalue b)
        {-# LINE 19 "value.duck" #-}
        unvalue (ValCons 2 [a, b, c, d, e])
          = ValBindIO (unvalue a) (unvalue b) (unvalue c) (unvalue d)
              (unvalue e)
        {-# LINE 19 "value.duck" #-}
        unvalue _ = undefined
