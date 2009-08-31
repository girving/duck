{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | Duck interpreter values

-- For now, this is dynamically typed

module Value
  ( Env
  , Value(..)
  , TValue
  , valUnit
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Var
import Type
import Prims
import Pretty
import qualified Lir
import Data.Map (Map)
import qualified Data.Map as Map

data Value
  = ValInt !Int
  | ValChr !Char
  | ValCons !CVar [Value] -- ^ Constructed data
  | ValClosure !Var [TValue] -- ^ Partially applied function (note that values are post-trans, and types are pre-trans)
  | ValDelay Env Lir.Exp -- ^ Delay (lazy) evaluation
  | ValType
    -- Monadic IO
  | ValLiftIO !Value -- ^ lifted (returned) value within IO monad
  | ValPrimIO !PrimIO [Value] -- ^ Closure of unexecuted IO call
  | ValBindIO !Var !TValue Env Lir.Exp -- ^ Unexecuted IO binding

type TValue = (Value, Type)

type Env = Map Var TValue

valUnit :: Value
valUnit = ValCons (V "()") []

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValChr c) = (100, pretty (show c))
  pretty' (ValCons c []) = pretty' c
  pretty' (ValCons c fields) | isTuple c = (1,
    hcat $ intersperse (pretty ", ") $ map (guard 2) fields)
  pretty' (ValCons (V ":") [h,t]) = (100,
    brackets (hcat (intersperse (pretty ", ") $ map (guard 2) (h : extract t))))
    where
    extract (ValCons (V "[]") []) = []
    extract (ValCons (V ":") [h,t]) = h : extract t
    extract e = error ("invalid tail "++pshow e++" in list")
  pretty' (ValCons c fields) = (2, pretty c <+> sep (map (guard 3) fields))
  pretty' ValType = pretty' "_"
  -- pretty' (ValFun _ vl e) = -- conveniently ignore env
  --  (0, pretty "\\" <> prettylist vl <> pretty " -> " <> pretty e)
  pretty' (ValClosure v args) = (2, pretty v <+> sep (map (guard 3) args))
  pretty' (ValDelay _ e) = (2, pretty "delay" <+> guard 3 e)
  pretty' (ValLiftIO v) = (2, pretty "return" <+> guard 3 v)
  pretty' (ValPrimIO p []) = pretty' p
  pretty' (ValPrimIO p args) = (2, pretty p <+> sep (map (guard 3) args))
  pretty' (ValBindIO v d _ e) = (0,
    pretty v <+> pretty "<-" <+> guard 0 d $$ guard 0 e)

instance Pretty TValue where
  pretty' (v,t) = (0, guard 1 v <+> pretty "::" <+> guard 60 t)
