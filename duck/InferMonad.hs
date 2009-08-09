{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards, TypeSynonymInstances #-}
-- | Duck type inference monad

module InferMonad
  ( Infer
  , FunctionInfo
  , typeError
  , withFrame
  , runInfer
  , getInfer
  , updateInfer
  ) where

import Var
import Control.Monad.State hiding (guard)
import Control.Monad.Error hiding (guard)
import Util
import Type
import Lir (Overloads)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow hiding ((<+>))
import Control.Exception
import CallStack
import SrcLoc

-- Stores our current knowledge about the types of functions
type FunctionInfo = Map Var Overloads

type InferState = FunctionInfo

data TypeError = TypeError (CallStack Type) SrcLoc String

instance Error TypeError where
  strMsg = TypeError [] noLoc

newtype Infer a = Infer { unInfer :: StateT (CallStack Type, InferState) (ErrorT TypeError IO) a }
  deriving (Monad, MonadIO, MonadError TypeError, MonadInterrupt)

showError :: TypeError -> String
showError (TypeError stack loc msg) = showStack stack ++ "Type error: "++msg++(if hasLoc loc then " at " ++ show loc else [])

makeTypeError :: SrcLoc -> String -> Infer TypeError
makeTypeError loc msg = Infer $ get >.= \ (s,_) -> TypeError s loc msg

typeError :: SrcLoc -> String -> Infer a
typeError loc msg = throwError =<< makeTypeError loc msg

withFrame :: Var -> [Type] -> SrcLoc -> Infer a -> Infer a
withFrame f args loc e =
  handleE (\ (e :: AsyncException) -> die . showError =<< makeTypeError noLoc (show e))
    (Infer $ do
      (s,_) <- get
      when (length s > 10) (unInfer $ typeError noLoc "stack overflow")
      modify (first (CallFrame f args loc :))
      r <- unInfer e
      modify (first (const s))
      return r)

runInfer :: CallStack Type -> FunctionInfo -> Infer a -> IO (a, FunctionInfo)
runInfer stack info e = runErrorT (runStateT (unInfer e) (stack, info) >.= second snd) >>= either (die . showError) return

instance MonadState InferState Infer where
  get = snd =.< Infer get
  put = Infer . modify . second . const
  --modify = Infer . modify . second

getInfer :: Infer InferState
getInfer = get
updateInfer :: (InferState -> InferState) -> Infer ()
updateInfer = Infer . modify . second -- modify
