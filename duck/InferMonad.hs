{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards, TypeSynonymInstances, FlexibleContexts #-}
-- | Duck type inference monad

module InferMonad
  ( Infer
  , inferError
  , withGlobals
  , withFrame
  , getProg
  , runInferProg
  , rerunInfer
  , debugInfer
  -- * Resolvable substitution failures/type errors
  , TypeError
  , typeError, typeErrors, typeReError
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
inferError l m = Infer $ ReaderT $ \(_,s) -> 
  fatalIO $ msg $ StackMsg (reverse s) $ locMsg l m

withFrame :: Var -> [TypeVal] -> SrcLoc -> Infer a -> Infer a
withFrame f args loc e = Infer $ ReaderT $ \(p,s) -> do
  let frame = CallFrame f args loc
      r e = runReaderT (unInfer e) $ (p, frame : s)
  when (length s > 16) $ r $ inferError loc "stack overflow"
  handleE (\(e :: AsyncException) -> r $ inferError loc (show e)) $ -- catch real errors
    catchError (r e) $ \e ->
      throwError (e { msgStack = frame : msgStack e }) -- preprend frame to resolve errors

withGlobals :: TypeEnv -> Infer [(Var,TypeVal)] -> Infer TypeEnv
withGlobals g f = Infer $ ReaderT $ \(p,s) -> 
  foldr (uncurry insertVar) g =.< 
    runReaderT (unInfer f) (p{ progGlobalTypes = g },s)

runInfer :: (Prog, InferStack) -> Infer a -> IO (a, FunctionInfo)
runInfer ps@(prog,_) f =
  either (fatalIO . msg) return =<<
    runErrorT (runStateT (runReaderT (unInfer f) ps) (progOverloads prog))

runInferProg :: Infer TypeEnv -> Prog -> IO Prog
runInferProg f prog = do
  (g,o) <- runInfer (prog,[]) f
  return $ prog { progGlobalTypes = g, progOverloads = o }

-- |'rerunInfer' discards any extra function info computed during the extra inference.
rerunInfer :: (Prog, InferStack) -> Infer a -> IO a
rerunInfer ps f = fst =.< runInfer ps f

instance ProgMonad Infer where
  getProg = fst =.< ask

debugInfer :: Pretty m => m -> Infer ()
debugInfer m = Infer $ ask >>= \(_,s) -> liftIO $ do
  putStrLn $ pout $ punctuate ':' (map callFunction (reverse s)) <:> m


-- |Indicate a potentially recoverable substitution failure/type error that could be caught during overload resolution
typeError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a
typeError l m = throwError $ StackMsg [] $ locMsg l m

typeMismatch :: (Pretty a, Pretty b, MonadError TypeError m) => a -> String -> b -> m c
typeMismatch x op y = typeError noLoc $ "type mismatch:" <+> quoted x <+> op <+> quoted y <+> "failed"

typeErrors :: (Pretty s, Pretty s', MonadError TypeError m) => SrcLoc -> s -> [(s',TypeError)] -> m a
typeErrors l m tel = typeError l $ nestedPunct ':' m $ vcat $ map (uncurry (nestedPunct ':')) tel

typeReError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a -> m a
typeReError l m f = catchError f $ \te -> typeError l $ nestedPunct ':' m te
