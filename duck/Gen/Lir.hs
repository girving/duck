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
         | ExpInt !Int
         | ExpChar !Char
         | ExpVar !Var
         | ExpApply !Exp !Exp
         | ExpLet !Var !Exp !Exp
         | ExpCons !CVar ![Exp]
         | ExpCase !Var ![(Var, [Var], Exp)] !(Maybe Exp)
         | ExpPrim !Prim ![Exp]
         | ExpSpec !Exp !TypePat
         | ExpBind !Var !Exp !Exp
         | ExpReturn !Exp
 
{-# LINE 9 "lir.duck" #-}
instance Convert Exp where
        {-# LINE 9 "lir.duck" #-}
        value (ExpLoc a b) = ValCons 0 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpInt a) = ValCons 1 [value a]
        {-# LINE 9 "lir.duck" #-}
        value (ExpChar a) = ValCons 2 [value a]
        {-# LINE 9 "lir.duck" #-}
        value (ExpVar a) = ValCons 3 [value a]
        {-# LINE 9 "lir.duck" #-}
        value (ExpApply a b) = ValCons 4 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpLet a b c) = ValCons 5 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpCons a b) = ValCons 6 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpCase a b c) = ValCons 7 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpPrim a b) = ValCons 8 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpSpec a b) = ValCons 9 [value a, value b]
        {-# LINE 9 "lir.duck" #-}
        value (ExpBind a b c) = ValCons 10 [value a, value b, value c]
        {-# LINE 9 "lir.duck" #-}
        value (ExpReturn a) = ValCons 11 [value a]
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 0 [a, b]) = ExpLoc (unvalue a) (unvalue b)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 1 [a]) = ExpInt (unvalue a)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 2 [a]) = ExpChar (unvalue a)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 3 [a]) = ExpVar (unvalue a)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 4 [a, b]) = ExpApply (unvalue a) (unvalue b)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 5 [a, b, c])
          = ExpLet (unvalue a) (unvalue b) (unvalue c)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 6 [a, b]) = ExpCons (unvalue a) (unvalue b)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 7 [a, b, c])
          = ExpCase (unvalue a) (unvalue b) (unvalue c)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 8 [a, b]) = ExpPrim (unvalue a) (unvalue b)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 9 [a, b]) = ExpSpec (unvalue a) (unvalue b)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 10 [a, b, c])
          = ExpBind (unvalue a) (unvalue b) (unvalue c)
        {-# LINE 9 "lir.duck" #-}
        unvalue (ValCons 11 [a]) = ExpReturn (unvalue a)
        {-# LINE 9 "lir.duck" #-}
        unvalue _ = undefined
