{-# LANGUAGE PatternGuards #-}
-- Duck interpreter values

-- For now, this is dynamically typed

module Value
  ( Env
  , Value(..)
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Var
import Pretty
import Text.PrettyPrint
import qualified Lir
import Data.Map (Map)
import qualified Data.Map as Map

type Env = Map Var Value

data Value
  = ValInt Int
  | ValCons Var [Value]
  | ValClosure Var [Value]
    -- Monadic IO
  | ValLiftIO Value
  | ValPrimIO Lir.PrimIO [Value]
  | ValBindIO Var Value Lir.Exp
  deriving Show

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValCons c []) = pretty' c
  pretty' (ValCons c fields) | istuple c = (1,
    hcat $ intersperse (text ", ") $ map (guard 2) fields)
  pretty' (ValCons (V ":") [h,t]) = (100,
    brackets (hcat (intersperse (text ", ") $ map (guard 2) (h : extract t))))
    where
    extract (ValCons (V "[]") []) = []
    extract (ValCons (V ":") [h,t]) = h : extract t
    extract e = error ("invalid tail "++show (pretty e)++" in list")
  pretty' (ValCons c fields) = (2, pretty c <+> sep (map (guard 3) fields))
  -- pretty' (ValFun _ vl e) = -- conveniently ignore env
  --  (0, text "\\" <> hsep (map pretty vl) <> text " -> " <> pretty e)
  pretty' (ValClosure v args) = (2, pretty v <+> sep (map (guard 3) args))
  pretty' (ValLiftIO v) = (2, text "return" <+> guard 3 v)
  pretty' (ValPrimIO p []) = pretty' p
  pretty' (ValPrimIO p args) = (2, pretty p <+> sep (map (guard 3) args))
  pretty' (ValBindIO v d e) = (0,
    pretty v <+> text "<-" <+> guard 0 d $$ guard 0 e)

