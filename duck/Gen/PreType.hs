{- Generated from "preType.duck" automatically; do not edit! -}
 
{-# LINE 1 "preType.duck" #-}
module Gen.PreType where
{-# LINE 1 "preType.duck" #-}
import Memory
{-# LINE 6 "preType.duck" #-}
import Var
{-# LINE 7 "preType.duck" #-}
import SrcLoc
{-# LINE 8 "preType.duck" #-}
import Type
 
{-# LINE 14 "preType.duck" #-}
data PreTypePat = TpVar !Var
                | TpCons !(Vol PreDatatype) ![PreTypePat]
                | TpFun ![TypeFun PreTypePat]
                | TpVoid
 
{-# LINE 14 "preType.duck" #-}
instance Convert PreTypePat where
        {-# LINE 14 "preType.duck" #-}
        value (TpVar a) = valCons 0 [value a]
        {-# LINE 14 "preType.duck" #-}
        value (TpCons a b) = valCons 1 [value a, value b]
        {-# LINE 14 "preType.duck" #-}
        value (TpFun a) = valCons 2 [value a]
        {-# LINE 14 "preType.duck" #-}
        value (TpVoid) = valCons 3 []
        {-# LINE 14 "preType.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> TpVar (unsafeUnvalue (unsafeUnvalCons val))
                1
                  -> let {-# LINE 16 "preType.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in TpCons (unsafeUnvalue a) (unsafeUnvalue b)
                2 -> TpFun (unsafeUnvalue (unsafeUnvalCons val))
                3 -> TpVoid
                _ -> error "bad tag in unsafeUnvalue PreTypePat"
 
{-# LINE 20 "preType.duck" #-}
data PreDatatype = PreData !CVar !SrcLoc ![Var]
                           ![(Loc CVar, [PreTypePat])] ![Variance]
 
{-# LINE 20 "preType.duck" #-}
instance Convert PreDatatype where
        {-# LINE 20 "preType.duck" #-}
        value (PreData a b c d e)
          = valCons 0 [value a, value b, value c, value d, value e]
        {-# LINE 20 "preType.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 20 "preType.duck" #-}
                (a, b, c, d, e) = unsafeUnvalCons val
              in
              PreData (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                (unsafeUnvalue d)
                (unsafeUnvalue e)
