{- Generated from "lir.duck" automatically; do not edit! -}
 
{-# LINE 1 "lir.duck" #-}
module Gen.Lir where
{-# LINE 1 "lir.duck" #-}
import Memory
{-# LINE 3 "lir.duck" #-}
import Var
{-# LINE 4 "lir.duck" #-}
import Type
{-# LINE 5 "lir.duck" #-}
import SrcLoc
{-# LINE 6 "lir.duck" #-}
import Prims
 
{-# LINE 9 "lir.duck" #-}
data Exp = ExpLoc !SrcLoc !Exp
         | ExpVal !TypeVal !Value
         | ExpVar !Var
         | ExpApply !Exp !Exp
         | ExpLet !Var !Exp !Exp
         | ExpCons !Datatype !Int ![Exp]
         | ExpCase !Var ![(Var, [Var], Exp)] !(Maybe Exp)
         | ExpPrim !Prim ![Exp]
         | ExpSpec !Exp !TypePat
         | ExpBind !Var !Exp !Exp
         | ExpReturn !Exp
 
{-# LINE 9 "lir.duck" #-}
instance Convert Exp where
        {-# LINE 9 "lir.duck" #-}
        value (ExpLoc a b) = valCons 0 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpVal a b) = valCons 1 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpVar a) = valCons 2 [value a]
        {-# LINE 9 "lir.duck" #-}
        value (ExpApply a b) = valCons 3 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpLet a b c) = valCons 4 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpCons a b c) = valCons 5 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpCase a b c) = valCons 6 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpPrim a b) = valCons 7 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpSpec a b) = valCons 8 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpBind a b c) = valCons 9 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpReturn a) = valCons 10 [value a]
        {-# LINE 9 "lir.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0
                  -> let {-# LINE 10 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpLoc (unsafeUnvalue a) (unsafeUnvalue b)
                1
                  -> let {-# LINE 11 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpVal (unsafeUnvalue a) (unsafeUnvalue b)
                2 -> ExpVar (unsafeUnvalue (unsafeUnvalCons val))
                3
                  -> let {-# LINE 13 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpApply (unsafeUnvalue a) (unsafeUnvalue b)
                4
                  -> let {-# LINE 14 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpLet (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                5
                  -> let {-# LINE 15 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpCons (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                6
                  -> let {-# LINE 16 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpCase (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                7
                  -> let {-# LINE 17 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpPrim (unsafeUnvalue a) (unsafeUnvalue b)
                8
                  -> let {-# LINE 18 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpSpec (unsafeUnvalue a) (unsafeUnvalue b)
                9
                  -> let {-# LINE 20 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpBind (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                10 -> ExpReturn (unsafeUnvalue (unsafeUnvalCons val))
                _ -> error "bad tag in unsafeUnvalue Exp"
