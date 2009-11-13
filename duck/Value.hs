{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Duck interpreter values

-- For now, this is dynamically typed

module Value
  ( Env
  , Value(..), FunValue(..), IOValue(..)
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
import Pretty

-- Pull in definition of Value
import Gen.Value

-- Add instance declarations
deriving instance Show Value
deriving instance Show FunValue
deriving instance Show IOValue

type Env = Map Var Value

valUnit :: Value
valUnit = ValCons 0 []

-- Pretty printing

prettyval :: TypeVal -> Value -> Doc'
prettyval t (ValInt i) | t == typeInt = pretty' i
prettyval t (ValChar c) | t == typeChar = pretty' (show c)
prettyval (TyCons (V "List") [t]) v | Just v' <- extract v = pretty' $
  brackets $ 3 #> punctuate ',' (map (prettyval t) v')
  where
  extract (ValCons 0 _) = Just []
  extract (ValCons 1 [h,t]) = (h :) =.< extract t
  extract _ = Nothing
prettyval (TyCons (V "Type") [t]) _ = pretty' t
prettyval (TyFun _) (ValFun f) = case f of
  ValClosure v types args -> prettyop v (zip args types)
  ValDelay e _ -> prettyop "delay" [e]
prettyval (TyCons (V "IO") [t]) (ValIO io) = case io of
  ValLiftIO v -> prettyval t v
  ValPrimIO p [] -> pretty' $ primString p
  ValPrimIO IOPutChar [c] -> prettyop (V "ioPutChar") [prettyval typeChar c]
  ValBindIO v t d e _ -> 0 #> v <+> "<-" <+> (d,t) $$ pretty e
  _ -> pretty' "<unknown-prim-io>"
prettyval t v = error ("type mismatch in prettyval "++pout t++" "++show v)

instance Pretty (Value,TypeVal) where
  pretty' (v,t) = 2 #> prettyval t v <+> "::" <+> t

instance (Ord k, Pretty k) => Pretty (Map k Value, Map k TypeVal) where
  pretty' (v,t) = pretty' $ Map.intersectionWith (,) v t
