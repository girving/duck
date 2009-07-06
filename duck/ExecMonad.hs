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
import Pretty
import Text.PrettyPrint
import Control.Monad.State hiding (guard)
import Control.Exception
import Util

type Callstack = [(Var, [Value])]

newtype Exec a = Exec { unExec :: StateT Callstack IO a }
  deriving (Monad, MonadIO)

handleE :: Exception e => (forall a. e -> Exec a) -> Exec b -> Exec b
handleE h e = Exec (do
  s <- get
  mapStateT (handle (\e -> evalStateT (unExec (h e)) s)) (unExec e))

withFrame :: Var -> [Value] -> Exec a -> Exec a
withFrame f args e =
  handleE (\ (e :: AsyncException) -> execError (show e))
  (Exec (do
    s <- get
    put ((f,args) : s)
    r <- unExec e
    put s
    return r))

runExec :: Exec a -> IO a
runExec e = evalStateT (unExec e) []

showStack :: Callstack -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (f,args) = "  in "++show (pretty f)++' ' : show (hsep (map (guard 2) args))

execError :: String -> Exec a
execError msg = Exec $ get >>= \s ->
  liftIO (die (showStack s ++ "Error: "++msg))
