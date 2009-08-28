{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types #-}
-- | Duck execution monad
--
-- Execution tracing monad.  This accomplishes:
--
-- (1) Hoisting duck IO out to haskell IO (not quite yet)
--
-- (2) Stack tracing

module ExecMonad
  ( Exec
  , withFrame
  , runExec
  , execError
  , liftInfer
  ) where

import Prelude hiding (catch)
import Control.Monad.State hiding (guard)
import Control.Exception

import Util
import Pretty
import Var
import Value
import SrcLoc
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

-- Most runtime errors should never happen, since they should be caught by type
-- inference and the like.  Therefore, we use exit status 3 so that they can be
-- distinguished from the better kinds of errors.
execError :: SrcLoc -> String -> Exec a
execError loc msg = Exec $ get >>= \s ->
  liftIO (dieWith 3 (pshow s ++ "\nRuntimeError: "++msg ++ (if hasLoc loc then " at " ++ show loc else [])))

liftInfer :: Lir.Prog -> Infer a -> Exec a
liftInfer prog infer = Exec $ do
  s <- get
  liftIO $ rerunInfer (mapStackArgs snd s) prog infer
