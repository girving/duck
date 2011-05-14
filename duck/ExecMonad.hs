{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types #-}
-- | Duck execution monad
--
-- Execution tracing monad.  This accomplishes:
--
-- (1) Hoisting duck IO out to haskell IO (not quite yet)
--
-- (2) Stack tracing
--
-- Should this be renamed to "InterpMonad" or is it more general?

module ExecMonad
  ( Exec
  , withFrame
  , runExec
  , execError
  , liftInfer
  ) where

import Prelude hiding (catch)
import Control.Monad.Reader
import Control.Exception

import Util
import Pretty
import Memory
import Var
import Stage
import Type
import Value()
import SrcLoc
import InferMonad hiding (withFrame)
import Lir (Prog, ProgMonad)
import Prettyval()

type ExecStack = CallStack (TypeVal,Value)

newtype Exec a = Exec { unExec :: ReaderT (Prog, ExecStack) IO a }
  deriving (Monad, MonadIO, MonadReader (Prog, ExecStack), MonadInterrupt)

-- Most runtime errors should never happen, since they should be caught by type
-- inference and the like.  Therefore, we use exit status 3 so that they can be
-- distinguished from the better kinds of errors.
execError :: Pretty s => SrcLoc -> s -> Exec a
execError l m = do
  s <- snd =.< ask
  fatalIO $ stageMsg StageExec noLoc $ StackMsg (reverse s) $ locMsg l m

withFrame :: Var -> [TypeVal] -> [Value] -> SrcLoc -> Exec a -> Exec a
withFrame f types args loc e = do
  let r = local $ second (CallFrame f (zipWith (,) types args) loc :)
  s <- snd =.< ask
  when (length s > 64) $ r $ execError loc "stack overflow"
  handleE (\(e :: AsyncException) -> r $ execError loc (show e)) $
    r e

instance ProgMonad Exec where
  getProg = fst =.< ask

runExec :: Prog -> Exec a -> IO a
runExec p e = runReaderT (unExec e) (p,[])

liftInfer :: Infer a -> Exec a
liftInfer infer = do
  (p, s) <- ask
  liftIO $ rerunInfer (p, mapStackArgs fst s) infer
