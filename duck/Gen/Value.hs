{- Generated from "value.duck" automatically; do not edit! -}
 
{-# LINE 1 "value.duck" #-}
module Gen.Value where
{-# LINE 3 "value.duck" #-}
import Var
{-# LINE 4 "value.duck" #-}
import Type
{-# LINE 5 "value.duck" #-}
import Lir
{-# LINE 6 "value.duck" #-}
import Prims
 
{-# LINE 16 "value.duck" #-}
data Value = ValInt !Int
           | ValChar !Char
           | ValCons !Int ![Value]
           | ValClosure !Var ![TypeVal] ![Value]
           | ValDelay !Exp ![(Var, TypeVal, Value)]
           | ValLiftIO !Value
           | ValPrimIO !Prim ![Value]
           | ValBindIO !Var !TypeVal !Value !Exp ![(Var, TypeVal, Value)]
