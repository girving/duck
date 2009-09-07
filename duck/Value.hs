{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

-- For now, this is dynamically typed

module Value
  ( Env
  , Value(..)
  , valUnit
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

import Util
import Var
import Type
import Prims
import Pretty
import ParseOps

-- Pull in definition of Value
import Gen.Value

type Env = Map Var Value

valUnit :: Value
valUnit = ValCons (V "()") []

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValChar c) = pretty' (show c)
  pretty' (ValCons (V ":") [h,t]) | Just t' <- extract t = pretty' $
    brackets $ 3 #> punctuate ',' (h : t')
    where
    extract (ValCons (V "[]") []) = Just []
    extract (ValCons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
  pretty' (ValCons c fields) = prettyop c fields
  pretty' ValType = pretty' '_'
  pretty' (ValClosure v types args) = prettyop v (zip args types)
  pretty' (ValDelay e _) = prettyop "delay" [e]
  pretty' (ValLiftIO v) = prettyop "return" [v]
  pretty' (ValPrimIO p args) = prettyop (V (primString p)) args
  pretty' (ValBindIO v t d e _) = 0 #>
    v <+> "<-" <+> (d,t) $$ pretty e

instance Pretty (Value,TypeVal) where
  pretty' (v,t) = 2 #> v <+> "::" <+> t
