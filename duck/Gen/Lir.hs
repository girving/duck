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
 
{-# LINE 11 "lir.duck" #-}
data Exp = ExpLoc !SrcLoc !Exp
         | ExpAtom !Atom
         | ExpApply !Exp !Exp
         | ExpLet !Var !Exp !Exp
         | ExpCons !Datatype !Int ![Exp]
         | ExpCase !Atom ![(Var, [Var], Exp)] !(Maybe Exp)
         | ExpPrim !Prim ![Exp]
         | ExpSpec !Exp !TypePat
 
{-# LINE 11 "lir.duck" #-}
instance Convert Exp where
        {-# LINE 11 "lir.duck" #-}
        value (ExpLoc a b) = valCons 0 [value a, value b]
        {-# LINE 11 "lir.duck" #-}
        value (ExpAtom a) = valCons 1 [value a]
        {-# LINE 11 "lir.duck" #-}
        value (ExpApply a b) = valCons 2 [value a, value b]
        {-# LINE 11 "lir.duck" #-}
        value (ExpLet a b c) = valCons 3 [value a, value b, value c]
        {-# LINE 11 "lir.duck" #-}
        value (ExpCons a b c) = valCons 4 [value a, value b, value c]
        {-# LINE 11 "lir.duck" #-}
        value (ExpCase a b c) = valCons 5 [value a, value b, value c]
        {-# LINE 11 "lir.duck" #-}
        value (ExpPrim a b) = valCons 6 [value a, value b]
        {-# LINE 11 "lir.duck" #-}
        value (ExpSpec a b) = valCons 7 [value a, value b]
        {-# LINE 11 "lir.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0
                  -> let {-# LINE 12 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpLoc (unsafeUnvalue a) (unsafeUnvalue b)
                1 -> ExpAtom (unsafeUnvalue (unsafeUnvalCons val))
                2
                  -> let {-# LINE 14 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpApply (unsafeUnvalue a) (unsafeUnvalue b)
                3
                  -> let {-# LINE 15 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpLet (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                4
                  -> let {-# LINE 16 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpCons (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                5
                  -> let {-# LINE 17 "lir.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in ExpCase (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                6
                  -> let {-# LINE 18 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpPrim (unsafeUnvalue a) (unsafeUnvalue b)
                7
                  -> let {-# LINE 19 "lir.duck" #-}
                         (a, b) = unsafeUnvalCons val
                       in ExpSpec (unsafeUnvalue a) (unsafeUnvalue b)
                _ -> error "bad tag in unsafeUnvalue Exp"
 
{-# LINE 21 "lir.duck" #-}
data Atom = AtomVal !TypedValue
          | AtomLocal !Var
          | AtomGlobal !Var
 
{-# LINE 21 "lir.duck" #-}
instance Convert Atom where
        {-# LINE 21 "lir.duck" #-}
        value (AtomVal a) = valCons 0 [value a]
        {-# LINE 21 "lir.duck" #-}
        value (AtomLocal a) = valCons 1 [value a]
        {-# LINE 21 "lir.duck" #-}
        value (AtomGlobal a) = valCons 2 [value a]
        {-# LINE 21 "lir.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> AtomVal (unsafeUnvalue (unsafeUnvalCons val))
                1 -> AtomLocal (unsafeUnvalue (unsafeUnvalCons val))
                2 -> AtomGlobal (unsafeUnvalue (unsafeUnvalCons val))
                _ -> error "bad tag in unsafeUnvalue Atom"
