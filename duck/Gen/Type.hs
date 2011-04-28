{- Generated from "type.duck" automatically; do not edit! -}
 
{-# LINE 1 "type.duck" #-}
module Gen.Type where
{-# LINE 1 "type.duck" #-}
import Memory
{-# LINE 6 "type.duck" #-}
import Var
{-# LINE 7 "type.duck" #-}
import SrcLoc
 
{-# LINE 21 "type.duck" #-}
data TypeFun t = FunArrow !t !t
               | FunClosure !Var ![t]
 
{-# LINE 21 "type.duck" #-}
instance (Convert t) => Convert (TypeFun t) where
        {-# LINE 21 "type.duck" #-}
        value (FunArrow a b) = ValCons 0 [value a, value b]
        {-# LINE 21 "type.duck" #-}
        value (FunClosure a b) = ValCons 1 [value a, value b]
        {-# LINE 21 "type.duck" #-}
        unvalue (ValCons 0 [a, b]) = FunArrow (unvalue a) (unvalue b)
        {-# LINE 21 "type.duck" #-}
        unvalue (ValCons 1 [a, b]) = FunClosure (unvalue a) (unvalue b)
        {-# LINE 21 "type.duck" #-}
        unvalue _ = undefined
 
{-# LINE 28 "type.duck" #-}
data TypeVal = TyCons !CVar ![TypeVal]
             | TyFun ![TypeFun TypeVal]
             | TyVoid
 
{-# LINE 28 "type.duck" #-}
instance Convert TypeVal where
        {-# LINE 28 "type.duck" #-}
        value (TyCons a b) = ValCons 0 [value a, value b]
        {-# LINE 28 "type.duck" #-}
        value (TyFun a) = ValCons 1 [value a]
        {-# LINE 28 "type.duck" #-}
        value (TyVoid) = ValCons 2 []
        {-# LINE 28 "type.duck" #-}
        unvalue (ValCons 0 [a, b]) = TyCons (unvalue a) (unvalue b)
        {-# LINE 28 "type.duck" #-}
        unvalue (ValCons 1 [a]) = TyFun (unvalue a)
        {-# LINE 28 "type.duck" #-}
        unvalue (ValCons 2 []) = TyVoid
        {-# LINE 28 "type.duck" #-}
        unvalue _ = undefined
 
{-# LINE 35 "type.duck" #-}
data TypePat = TsVar !Var
             | TsCons !CVar ![TypePat]
             | TsFun ![TypeFun TypePat]
             | TsVoid
 
{-# LINE 35 "type.duck" #-}
instance Convert TypePat where
        {-# LINE 35 "type.duck" #-}
        value (TsVar a) = ValCons 0 [value a]
        {-# LINE 35 "type.duck" #-}
        value (TsCons a b) = ValCons 1 [value a, value b]
        {-# LINE 35 "type.duck" #-}
        value (TsFun a) = ValCons 2 [value a]
        {-# LINE 35 "type.duck" #-}
        value (TsVoid) = ValCons 3 []
        {-# LINE 35 "type.duck" #-}
        unvalue (ValCons 0 [a]) = TsVar (unvalue a)
        {-# LINE 35 "type.duck" #-}
        unvalue (ValCons 1 [a, b]) = TsCons (unvalue a) (unvalue b)
        {-# LINE 35 "type.duck" #-}
        unvalue (ValCons 2 [a]) = TsFun (unvalue a)
        {-# LINE 35 "type.duck" #-}
        unvalue (ValCons 3 []) = TsVoid
        {-# LINE 35 "type.duck" #-}
        unvalue _ = undefined
 
{-# LINE 59 "type.duck" #-}
data Variance = Covariant
              | Invariant
 
{-# LINE 59 "type.duck" #-}
instance Convert Variance where
        {-# LINE 59 "type.duck" #-}
        value (Covariant) = ValCons 0 []
        {-# LINE 59 "type.duck" #-}
        value (Invariant) = ValCons 1 []
        {-# LINE 59 "type.duck" #-}
        unvalue (ValCons 0 []) = Covariant
        {-# LINE 59 "type.duck" #-}
        unvalue (ValCons 1 []) = Invariant
        {-# LINE 59 "type.duck" #-}
        unvalue _ = undefined
 
{-# LINE 62 "type.duck" #-}
data Trans = Delayed
 
{-# LINE 62 "type.duck" #-}
instance Convert Trans where
        {-# LINE 62 "type.duck" #-}
        value (Delayed) = ValCons 0 []
        {-# LINE 62 "type.duck" #-}
        unvalue (ValCons 0 []) = Delayed
        {-# LINE 62 "type.duck" #-}
        unvalue _ = undefined
 
{-# LINE 66 "type.duck" #-}
data Datatype = Data !CVar !SrcLoc ![Var] ![(Loc CVar, [TypePat])]
                     ![Variance]
 
{-# LINE 66 "type.duck" #-}
instance Convert Datatype where
        {-# LINE 66 "type.duck" #-}
        value (Data a b c d e)
          = ValCons 0 [value a, value b, value c, value d, value e]
        {-# LINE 66 "type.duck" #-}
        unvalue (ValCons 0 [a, b, c, d, e])
          = Data (unvalue a) (unvalue b) (unvalue c) (unvalue d) (unvalue e)
        {-# LINE 66 "type.duck" #-}
        unvalue _ = undefined
