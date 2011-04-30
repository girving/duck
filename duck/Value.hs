{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

-- For now, this is dynamically typed

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

prettyval :: TypeVal -> Value -> Doc'
prettyval t v | t == typeInt = pretty' (unsafeUnvalue v :: Int)
prettyval t v | t == typeChar = pretty' (unsafeUnvalue v :: Char)
prettyval (TyCons (V "List") [t]) v = pretty' $
  brackets $ 3 #> punctuate ',' (map (prettyval t) v')
  where v' = unsafeUnvalue v :: [Value]
prettyval (TyCons (V "Type") [t]) _ = pretty' t
prettyval (TyFun _) v = pretty' (unsafeUnvalue v :: FunValue)
prettyval (TyCons (V "IO") [t]) v = prettyio t (unsafeUnvalue v :: IOValue)
prettyval t v = error ("type mismatch in prettyval "++pout t++" "++show v)

instance Pretty FunValue where
  pretty' (ValClosure v types args) = prettyop v (zip args types)
  pretty' (ValDelay e _) = prettyop "delay" [e]

prettyio :: TypeVal -> IOValue -> Doc'
prettyio t (ValLiftIO v) = prettyval t v
prettyio _ (ValPrimIO p []) = pretty' $ primString p
prettyio _ (ValPrimIO IOPutChar [c]) = prettyop (V "ioPutChar") [prettyval typeChar c]
prettyio _ (ValBindIO v t d e _) = 0 #> v <+> "<-" <+> (d,t) $$ pretty e
prettyio _ _ = pretty' "<unknown-prim-io>"

instance Pretty (Value,TypeVal) where
  pretty' (v,t) = 2 #> prettyval t v <+> "::" <+> t

instance Pretty (IOValue,TypeVal) where
  pretty' (v,t) = 2 #> prettyio t v <+> "::" <+> t

instance (Ord k, Pretty k) => Pretty (Map k Value, Map k TypeVal) where
  pretty' (v,t) = pretty' $ Map.intersectionWith (,) v t
