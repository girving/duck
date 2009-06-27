{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards #-}
-- Duck type inference monad

module InferMonad
  ( Infer
  , insert
  , lookup
  , typeError
  ) where

import Prelude hiding (catch, lookup)
import Var
import Control.Monad.State hiding (guard)
import Util
import Type
import Ptrie (Ptrie')
import qualified Ptrie
import Data.Map (Map)
import qualified Data.Map as Map

-- Stores our current knowledge about the types of functions
type FunctionInfo = Map Var (Ptrie' Type Type)

newtype Infer a = Infer (StateT FunctionInfo IO a)
  deriving Monad

insert :: Var -> [Type] -> Type -> Infer ()
insert f tl r = (Infer . modify) (Map.alter (Ptrie.insert tl r) f)

lookup :: Var -> [Type] -> Infer (Maybe Type)
lookup f tl = Infer get >>=. \info ->
  case Ptrie.lookup tl (Map.lookup f info) of
    Nothing -> Nothing -- no match, type not yet inferred
    Just p | Just t <- Ptrie.unleaf' p -> Just t -- fully applied
    Just _ -> Just (TyApply f tl)

typeError :: String -> Infer a
typeError msg = Infer $ get >>= \_ ->
  liftIO (die ("Type error: "++msg))
