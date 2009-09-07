{- Generated from "srcLoc.duck" automatically; do not edit! -}
 
{-# LINE 1 "srcLoc.duck" #-}
module Gen.SrcLoc where
 
{-# LINE 3 "srcLoc.duck" #-}
data SrcLoc = SrcNone ![Char]
            | SrcLoc ![Char] !Int !Int
            | SrcRng ![Char] !Int !Int !Int !Int
