{- Generated from "lir.duck" automatically; do not edit! -}
 
{-# LINE 1 "lir.duck" #-}
module Gen.Lir where
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
