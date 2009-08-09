{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types #-}
-- | Duck execution monad

module ExecMonad
  ( Exec
  , withFrame
  , runExec
  , execError
  , liftInfer
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
import Util
import CallStack
import InferMonad hiding (withFrame)
import qualified Lir

newtype Exec a = Exec { unExec :: StateT (CallStack TValue) IO a }
  deriving (Monad, MonadIO, MonadInterrupt)

withFrame :: Var -> [TValue] -> SrcLoc -> Exec a -> Exec a
withFrame f args loc e =
  handleE (\ (e :: AsyncException) -> execError loc (show e))
  (Exec (do
    s <- get
    put (CallFrame f args loc : s)
    r <- unExec e
    put s
    return r))

runExec :: Exec a -> IO a
runExec e = evalStateT (unExec e) []

execError :: SrcLoc -> String -> Exec a
execError loc msg = Exec $ get >>= \s ->
  liftIO (die (showStack s ++ "RuntimeError: "++msg ++ (if hasLoc loc then " at " ++ show loc else [])))

liftInfer :: Lir.Prog -> Infer a -> Exec a
liftInfer prog infer = Exec $ do
  s <- get
  let info = Lir.progOverloads prog
  (r,_info') <- liftIO $ runInfer (mapStackArgs snd s) info infer
  -- when (info /= info') $ die (showStack s ++ "RuntimeError: inference changed overload table")
  return r
