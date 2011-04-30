{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

module Value
  ( Env
  , FunValue(..), IOValue(..)
  , valEmpty
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

import Var
import Type
import Prims
import Pretty
import ParseOps
import SrcLoc
import Memory

-- Pull in definition of IOValue and FunValue
import Gen.Value

-- Add instance declarations
deriving instance Show FunValue
deriving instance Show IOValue

type Env = Map Var Value

valEmpty :: Value
valEmpty = valCons 0 []

-- Pretty printing

prettyval :: Datatypes -> TypeVal -> Value -> Doc'
prettyval _ t v | t == typeInt = pretty' (unsafeUnvalue v :: Int)
prettyval _ t v | t == typeChar = pretty' (unsafeUnvalue v :: Char)
prettyval denv (TyCons (V "List") [t]) v = pretty' $
  brackets $ 3 #> punctuate ',' (map (prettyval denv t) v')
  where v' = unsafeUnvalue v :: [Value]
prettyval _ (TyCons (V "Type") [t]) _ = pretty' t
prettyval denv (TyFun _) v = prettyfun denv (unsafeUnvalue v :: FunValue)
prettyval denv (TyCons (V "IO") [t]) v = prettyio denv t (unsafeUnvalue v :: IOValue)
prettyval denv (TyCons tc args) v = case Map.lookup tc denv of
  Just (Data _ _ vl conses _) -> prettyop c (zipWith (prettyval denv) tl' values) where
    (L _ c,tl) = conses !! unsafeTag v
    tenv = Map.fromList (zip vl args)
    tl' = map (substVoid tenv) tl
    values = unsafeUnvalConsN (length tl) v
  Nothing -> error ("unbound datatype "++show tc++" in prettyval")
prettyval _ TyVoid _ = error "found an impossible Void value in prettyval"

instance Pretty (Datatypes, TypeVal, Value) where
  pretty' (denv,t,v) = 2 #> prettyval denv t v <+> "::" <+> t

prettyfun :: Datatypes -> FunValue -> Doc'
prettyfun denv (ValClosure v types args) = prettyop v (zipWith (prettyval denv) types args)
prettyfun _ (ValDelay e _) = prettyop "delay" [e]

instance Pretty (Datatypes, FunValue) where
  pretty' (denv, v) = prettyfun denv v

prettyio :: Datatypes -> TypeVal -> IOValue -> Doc'
prettyio denv t (ValLiftIO v) = pretty' (denv,t,v)
prettyio _ _ (ValPrimIO p []) = pretty' $ primString p
prettyio denv _ (ValPrimIO IOPutChar [c]) = prettyop (V "ioPutChar") [prettyval denv typeChar c]
prettyio denv _ (ValBindIO v t d e _) = 0 #> v <+> "<-" <+> (denv,t,d) $$ pretty e
prettyio _ _ (ValPrimIO _ _) = pretty' "<unknown-prim-io>"

instance Pretty (Datatypes, TypeVal, IOValue) where
  pretty' (denv,t,v) = prettyio denv t v

instance (Ord k, Pretty k) => Pretty (Datatypes, Map k TypeVal, Map k Value) where
  pretty' (denv,t,v) = pretty' $ Map.intersectionWith (\t v -> (denv,t,v)) t v
