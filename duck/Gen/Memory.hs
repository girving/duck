{- Generated from "memory.duck" automatically; do not edit! -}
 
{-# LINE 1 "memory.duck" #-}
module Gen.Memory where
 
{-# LINE 6 "memory.duck" #-}
data Value = ValInt !Int
           | ValChar !Char
           | ValCons !Int ![Value]
