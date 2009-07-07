{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types #-}
-- | Duck execution monad

module ExecMonad
  ( Exec
  , withFrame
  , runExec
  , execError
  ) where

-- Execution tracing monad.  This accomplishes
--   1. Hoisting duck IO out to haskell IO (not quite yet)
--   2. Stack tracing

import Prelude hiding (catch)
import Var
import Value
import SrcLoc
import Pretty
import Text.PrettyPrint
import Control.Monad.State hiding (guard)
import Control.Exception
import Util

data CallFrame = CallFrame 
  { callFunction :: Var
  , callArgs :: [Value]
  , callLoc :: SrcLoc
  }

type CallStack = [CallFrame]

newtype Exec a = Exec { unExec :: StateT CallStack IO a }
  deriving (Monad, MonadIO)

handleE :: Exception e => (forall a. e -> Exec a) -> Exec b -> Exec b
handleE h e = Exec (do
  s <- get
  mapStateT (handle (\e -> evalStateT (unExec (h e)) s)) (unExec e))

withFrame :: Var -> [Value] -> SrcLoc -> Exec a -> Exec a
withFrame f args loc e =
  handleE (\ (e :: AsyncException) -> execError loc (show e))
  (Exec (do
    s <- get
    put ((CallFrame f args loc) : s)
    r <- unExec e
    put s
    return r))

runExec :: Exec a -> IO a
runExec e = evalStateT (unExec e) []

showStack :: CallStack -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (CallFrame f args loc) = "  " ++ show loc ++ " in "++show (pretty f)++' ' : show (hsep (map (guard 2) args))

execError :: SrcLoc -> String -> Exec a
execError loc msg = Exec $ get >>= \s ->
  liftIO (die (showStack s ++ "Error: "++msg ++ (if hasLoc loc then " at " ++ show loc else [])))
