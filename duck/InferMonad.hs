{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards, TypeSynonymInstances, FlexibleContexts #-}
-- | Duck type inference monad

module InferMonad
  ( Infer
  , inferError
  , withFrame
  , getProg
  , runInferProg
  , rerunInfer
  , debugInfer
  -- * Resolvable substitution failures/type errors
  , TypeError
  , typeError, typeReError
  , typeMismatch
  ) where

import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State hiding (guard)
import Control.Monad.Error hiding (guard)
import Control.Exception

import Util
import Var
import Pretty
import Stage
import Type
import Lir
import SrcLoc
import TypedValue ()

type InferStack = CallStack TypeVal

-- |Stores our current knowledge about the types of functions
type FunctionInfo = Map Var Overloads

-- |Type errors that may be resolvable substitution failures
type TypeError = StackMsg TypeVal

instance Error TypeError where
  strMsg = StackMsg [] . msg

newtype Infer a = Infer { unInfer :: ReaderT (Prog, InferStack) (StateT FunctionInfo (ErrorT TypeError IO)) a }
  deriving (Monad, MonadIO, MonadReader (Prog, InferStack), MonadState FunctionInfo, MonadError TypeError, MonadInterrupt)

-- |Indicate a fatal error in inference (one that cannot be resolved by a different overload path)
inferError :: Pretty s => SrcLoc -> s -> Infer a
inferError l m = do
  s <- snd =.< ask
  fatalIO $ msg $ StackMsg (reverse s) $ locMsg l m

withFrame :: Var -> [TypeVal] -> SrcLoc -> Infer a -> Infer a
withFrame f args loc e = do
  let frame = CallFrame f args loc
      r = local $ second (frame :)
  s <- snd =.< ask
  when (length s > 32) $ r $ inferError loc "stack overflow"
  handleE (\(e :: AsyncException) -> r $ inferError loc (show e)) $ -- catch real errors
    catchError (r e) $ \e ->
      throwError (e { msgStack = frame : msgStack e }) -- preprend frame to resolve errors

runInfer :: (Prog, InferStack) -> Infer a -> IO (a, FunctionInfo)
runInfer ps@(prog,_) f =
  either (fatalIO . msg) return =<<
    runErrorT (runStateT (runReaderT (unInfer f) ps) (progOverloads prog))

runInferProg :: Infer GlobalTypes -> Prog -> IO Prog
runInferProg f prog = do
  (g,o) <- runInfer (prog,[]) f
  return $ prog { progGlobalTypes = g, progOverloads = o }

-- |'rerunInfer' discards any extra function info computed during the extra inference.
rerunInfer :: (Prog, InferStack) -> Infer a -> IO a
rerunInfer ps f = fst =.< runInfer ps f

instance ProgMonad Infer where
  getProg = fst =.< ask

debugInfer :: Pretty m => m -> Infer ()
debugInfer m = do
  s <- snd =.< ask
  liftIO $ putStrLn $ pout $ punctuate ':' (map callFunction (reverse s)) <:> m

-- |Indicate a potentially recoverable substitution failure/type error that could be caught during overload resolution
typeError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a
typeError l m = throwError $ StackMsg [] $ locMsg l m

typeMismatch :: (Pretty a, Pretty b, MonadError TypeError m) => a -> String -> b -> m c
typeMismatch x op y = typeError noLoc $ "type mismatch:" <+> quoted x <+> op <+> quoted y <+> "failed"

typeReError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a -> m a
typeReError l m f = catchError f $ \te -> typeError l $ nestedPunct ':' m te
