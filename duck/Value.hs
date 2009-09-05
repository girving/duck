{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
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
import qualified Lir
import ParseOps

data Value
  = ValInt !Int
  | ValChr !Char
  | ValCons !CVar ![Value] -- ^ Constructed data
  | ValClosure !Var ![Type] ![Value] -- ^ Partially applied function (note that values are post-trans, and types are pre-trans)
  | ValDelay !TypeEnv !Env !Lir.Exp -- ^ Delay (lazy) evaluation
  | ValType
    -- Monadic IO
  | ValLiftIO !Value -- ^ lifted (returned) value within IO monad
  | ValPrimIO !Prim ![Value] -- ^ Closure of unexecuted IO call
  | ValBindIO !Var !Type !Value !TypeEnv !Env !Lir.Exp -- ^ Unexecuted IO binding

type Env = Map Var Value

valUnit :: Value
valUnit = ValCons (V "()") []

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValChr c) = pretty' (show c)
  pretty' (ValCons (V ":") [h,t]) | Just t' <- extract t = pretty' $
    brackets $ 3 #> punctuate ',' (h : t')
    where
    extract (ValCons (V "[]") []) = Just []
    extract (ValCons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
  pretty' (ValCons c fields) = prettyop c fields
  pretty' ValType = pretty' '_'
  pretty' (ValClosure v types args) = prettyop v (zip args types)
  pretty' (ValDelay _ _ e) = prettyop "delay" [e]
  pretty' (ValLiftIO v) = prettyop "return" [v]
  pretty' (ValPrimIO p args) = prettyop (V (primString p)) args
  pretty' (ValBindIO v t d _ _ e) = 0 #>
    v <+> "<-" <+> (d,t) $$ pretty e

instance Pretty (Value,Type) where
  pretty' (v,t) = 2 #> v <+> "::" <+> t
