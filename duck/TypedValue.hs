{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}

module TypedValue
  ( Any(..)
  , prettyval
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid hiding (Any)

import Memory
import ParseOps
import Pretty
import Prims
import SrcLoc
import Type
import Value
import Var

-- | Pretty printing for values

prettyval :: TypeVal -> Value -> Doc'
prettyval t v | t == typeInt = pretty' (unsafeUnvalue v :: Int)
prettyval t v | t == typeChar = pretty' (show (unsafeUnvalue v :: Char))
prettyval (TyCons d [t]) v | V "List" == dataName d && t == typeChar =
  pretty' (show (unsafeUnvalue v :: [Char]))
prettyval (TyCons d [t]) v | V "List" == dataName d = pretty' $
  brackets $ 3 #> punctuate ',' (map (prettyval t) v')
  where v' = unsafeUnvalue v :: [Value]
prettyval (TyFun _) v 
  | ValClosure v types args <- unsafeUnvalue v
  = prettyop v (zipWith prettyval types args)
prettyval (TyCons d [t]) _
  | d == datatypeType = pretty' t
  | d == datatypeDelay = pretty' "<delay>"
prettyval (TyCons d args) v = case dataInfo d of
  DataAlgebraic conses -> prettyop c (zipWith prettyval tl' values) where
    (L _ c,tl) = conses !! unsafeTag v
    tenv = Map.fromList (zip (dataTyVars d) args)
    tl' = map (substVoid tenv) tl
    values = unsafeUnvalConsN (length tl) v
  DataPrim _ -> error ("don't know how to print primitive datatype "++show (quoted d))
prettyval (TyStatic (Any t _)) d = prettyval t d
prettyval TyVoid _ = error "found an impossible Void value in prettyval"

instance Pretty Any where
  pretty' (Any t v) = 2 #> prettyval t v <+> "::" <+> t

instance (Ord k, Pretty k) => Pretty (Map k TypeVal, Map k Value) where
  pretty' (t, v) = pretty' $ Map.intersectionWith Any t v

compareval :: TypeVal -> Value -> Value -> Ordering
compareval (TyCons d args) v1 v2 = cmpd (dataInfo d) where
  cmpd (DataAlgebraic conses) =
    compare c1 (unsafeTag v2) `mappend`
      mconcat (zipWith3 compareval tl' vl1 vl2) where
    c1 = unsafeTag v1
    (_,tl) = conses !! c1
    tenv = Map.fromList (zip (dataTyVars d) args)
    tl' = map (substVoid tenv) tl
    vl1 = unsafeUnvalConsN (length tl) v1
    vl2 = unsafeUnvalConsN (length tl) v2
  cmpd (DataPrim 0) = EQ
  cmpd (DataPrim z) 
    | z == wordSize = compare v1 v2
    | otherwise = error $ "compare: unhandled primitive size " ++ show z
compareval (TyFun _) v1 v2 = 
  compare f1 f2 `mappend` 
    mconcat (zipWith compare (tv tl1 vl1) (tv tl2 vl2)) where
  tv = zipWith Any
  ValClosure f1 tl1 vl1 = unsafeUnvalue v1
  ValClosure f2 tl2 vl2 = unsafeUnvalue v2
compareval (TyStatic (Any t _)) v1 v2 = compareval t v1 v2
compareval TyVoid _ _ = error $ "compare: impossible Void value"

instance Ord Any where
  compare (Any t1 v1) (Any t2 v2) =
    compare t1 t2 `mappend` compareval t1 v1 v2

instance Eq Any where
  Any t1 v1 == Any t2 v2 = t1 == t2 && compareval t1 v1 v2 == EQ

-- now we can do these:

instance Pretty TypeVal where
  pretty' (TyStatic tv) = prettyap Static [tv]
  pretty' t = pretty' $ singleton t

deriving instance Eq TypeVal
deriving instance Ord TypeVal
