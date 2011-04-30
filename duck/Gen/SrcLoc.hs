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
        value (SrcNone a) = valCons 0 [value a]
        {-# LINE 3 "srcLoc.duck" #-}
        value (SrcLoc a b c) = valCons 1 [value a, value b, value c]
        {-# LINE 3 "srcLoc.duck" #-}
        value (SrcRng a b c d e)
          = valCons 2 [value a, value b, value c, value d, value e]
        {-# LINE 3 "srcLoc.duck" #-}
        unsafeUnvalue val
          = case unsafeTag val of
                0 -> SrcNone (unsafeUnvalue (unsafeUnvalCons val))
                1
                  -> let {-# LINE 5 "srcLoc.duck" #-}
                         (a, b, c) = unsafeUnvalCons val
                       in SrcLoc (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                2
                  -> let {-# LINE 6 "srcLoc.duck" #-}
                         (a, b, c, d, e) = unsafeUnvalCons val
                       in
                       SrcRng (unsafeUnvalue a) (unsafeUnvalue b) (unsafeUnvalue c)
                         (unsafeUnvalue d)
                         (unsafeUnvalue e)
                _ -> error "bad tag in unsafeUnvalue SrcLoc"
 
{-# LINE 8 "srcLoc.duck" #-}
data Loc a = L !SrcLoc !a
 
{-# LINE 8 "srcLoc.duck" #-}
instance (Convert a) => Convert (Loc a) where
        {-# LINE 8 "srcLoc.duck" #-}
        value (L a b) = valCons 0 [value a, value b]
        {-# LINE 8 "srcLoc.duck" #-}
        unsafeUnvalue val
          = let {-# LINE 9 "srcLoc.duck" #-}
                (a, b) = unsafeUnvalCons val
              in L (unsafeUnvalue a) (unsafeUnvalue b)
