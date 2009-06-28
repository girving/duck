{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards #-}
-- Duck type inference monad

module InferMonad
  ( Infer
  , insert
  , lookup
  , typeError
  , withFrame
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
import Pretty
import Text.PrettyPrint
import Control.Arrow

type Callstack = [(Var, [Type])]

-- Stores our current knowledge about the types of functions
type FunctionInfo = Map Var (Ptrie' Type Type)

newtype Infer a = Infer { unInfer :: (StateT (Callstack, FunctionInfo) IO a) }
  deriving Monad

insert :: Var -> [Type] -> Type -> Infer ()
insert f tl r = (Infer . modify) (second (Map.alter (Ptrie.insert tl r) f))

lookup :: Var -> [Type] -> Infer (Maybe Type)
lookup f tl = Infer get >.= \ (_,info) ->
  case Ptrie.lookup tl (Map.lookup f info) of
    Nothing -> Nothing -- no match, type not yet inferred
    Just p | Just t <- Ptrie.unleaf' p -> Just t -- fully applied
    Just _ -> Just (TyApply f tl)

showStack :: Callstack -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (f,args) = "  in "++show (pretty f)++' ' : show (hsep (map (guard 2) args))

typeError :: String -> Infer a
typeError msg = Infer $ get >>= \ (s,_) ->
  liftIO (die (showStack s ++ "Type error: "++msg))

withFrame :: Var -> [Type] -> Infer a -> Infer a
withFrame f args e = Infer $ do
  (s,_) <- get
  modify (first ((f,args):))
  r <- unInfer e
  modify (first (const s))
  return r
