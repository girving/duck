{- Generated from "srcLoc.duck" automatically; do not edit! -}
 
{-# LINE 1 "srcLoc.duck" #-}
module Gen.SrcLoc where
{-# LINE 1 "srcLoc.duck" #-}
import Memory
 
{-# LINE 3 "srcLoc.duck" #-}
data SrcLoc = SrcNone ![Char]
            | SrcLoc ![Char] !Int !Int
            | SrcRng ![Char] !Int !Int !Int !Int
 
{-# LINE 3 "srcLoc.duck" #-}
instance Convert SrcLoc where
        {-# LINE 3 "srcLoc.duck" #-}
        value (SrcNone a) = ValCons 0 [value a]
        {-# LINE 3 "srcLoc.duck" #-}
        value (SrcLoc a b c) = ValCons 1 [value a, value b, value c]
        {-# LINE 3 "srcLoc.duck" #-}
        value (SrcRng a b c d e)
          = ValCons 2 [value a, value b, value c, value d, value e]
        {-# LINE 3 "srcLoc.duck" #-}
        unvalue (ValCons 0 [a]) = SrcNone (unvalue a)
        {-# LINE 3 "srcLoc.duck" #-}
        unvalue (ValCons 1 [a, b, c])
          = SrcLoc (unvalue a) (unvalue b) (unvalue c)
        {-# LINE 3 "srcLoc.duck" #-}
        unvalue (ValCons 2 [a, b, c, d, e])
          = SrcRng (unvalue a) (unvalue b) (unvalue c) (unvalue d)
              (unvalue e)
        {-# LINE 3 "srcLoc.duck" #-}
        unvalue _ = undefined
