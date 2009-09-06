{- Generated from "type.duck" automatically; do not edit! -}
 
{-# LINE 1 "type.duck" #-}
module Gen.Type where
{-# LINE 6 "type.duck" #-}
import Var
 
{-# LINE 20 "type.duck" #-}
data TypeFun t = FunArrow !t !t
               | FunClosure !Var ![t]
 
{-# LINE 27 "type.duck" #-}
data TypeVal = TyCons !CVar ![TypeVal]
             | TyFun ![TypeFun TypeVal]
             | TyVoid
 
{-# LINE 34 "type.duck" #-}
data TypePat = TsVar !Var
             | TsCons !CVar ![TypePat]
             | TsFun ![TypeFun TypePat]
             | TsVoid
 
{-# LINE 58 "type.duck" #-}
data Variance = Covariant
              | Invariant
 
{-# LINE 61 "type.duck" #-}
data Trans = Delayed
