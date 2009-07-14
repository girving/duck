{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types #-}
-- | Duck execution monad

module ExecMonad
  ( Exec
  , withFrame
  , runExec
  , execError
  , liftInfer
  , GlobalTypes
  , getGlobalTypes
  ) where

-- Execution tracing monad.  This accomplishes
--   1. Hoisting duck IO out to haskell IO (not quite yet)
--   2. Stack tracing

import Prelude hiding (catch)
import Var
import Value
import SrcLoc
import Control.Monad.State hiding (guard)
import Control.Exception
import Control.Arrow hiding ((<+>))
import Util
import Callstack
import InferMonad hiding (withFrame)
import Type

type GlobalTypes = TypeEnv
type ExecState = (Callstack TValue, (GlobalTypes, FunctionInfo))

newtype Exec a = Exec { unExec :: StateT ExecState IO a }
  deriving (Monad, MonadIO, MonadInterrupt)

withFrame :: Var -> [TValue] -> SrcLoc -> Exec a -> Exec a
withFrame f args loc e =
  handleE (\ (e :: AsyncException) -> execError loc (show e))
  (Exec $ do
    (s,_) <- get
    modify (first (CallFrame f args loc:))
    r <- unExec e
    modify (first (const s))
    return r)

runExec :: (GlobalTypes, FunctionInfo) -> Exec a -> IO a
runExec info e = evalStateT (unExec e) ([],info)

execError :: SrcLoc -> String -> Exec a
execError loc msg = Exec $ get >>= \ (s,_) ->
  liftIO (die (showStack s ++ "RuntimeError: "++msg ++ (if hasLoc loc then " at " ++ show loc else [])))

liftInfer :: Infer a -> Exec a
liftInfer infer = Exec $ do
  (_,(_,info)) <- get
  (r,info) <- liftIO $ runInfer info infer
  modify (second (second (const info)))
  return r

getGlobalTypes :: Exec GlobalTypes
getGlobalTypes = Exec $ get >.= fst. snd
