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
import qualified Data.Map as Map
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

type InferStack = CallStack Type

-- |Stores our current knowledge about the types of functions
type FunctionInfo = Map Var Overloads

-- |Type errors that may be resolvable substitution failures
type TypeError = ErrorStack Type

instance Error TypeError where
  strMsg = ErrorStack [] noLoc . pretty

newtype Infer a = Infer { unInfer :: ReaderT (Prog, InferStack) (StateT FunctionInfo (ErrorT TypeError IO)) a }
  deriving (Monad, MonadIO, MonadReader (Prog, InferStack), MonadState FunctionInfo, MonadError TypeError, MonadInterrupt)

-- |Indicate a fatal error in inference (one that cannot be resolved by a different overload path)
inferError :: Pretty s => SrcLoc -> s -> Infer a
inferError l m = Infer $ ReaderT $ \(_,s) -> 
  stageErrorIO StageInfer noLoc $ ErrorStack (reverse s) l (pretty m)

withFrame :: Var -> [Type] -> SrcLoc -> Infer a -> Infer a
withFrame f args loc e = Infer $ ReaderT $ \(p,s) -> do
  let frame = CallFrame f args loc
      r e = runReaderT (unInfer e) $ (p, frame : s)
  when (length s > 16) $ r $ inferError loc "stack overflow"
  handleE (\(e :: AsyncException) -> r $ inferError loc (show e)) $ -- catch real errors
    catchError (r e) $ \e ->
      throwError (e { errStack = frame : errStack e }) -- preprend frame to resolve errors

withGlobals :: TypeEnv -> Infer [(Var,Type)] -> Infer TypeEnv
withGlobals g f = Infer $ ReaderT $ \(p,s) -> 
  foldr (uncurry Map.insert) g =.< 
    runReaderT (unInfer f) (p{ progGlobalTypes = g },s)

runInfer :: Stage -> (Prog, InferStack) -> Infer a -> IO (a, FunctionInfo)
runInfer st ps@(prog,_) f =
  either (stageErrorIO st noLoc) return =<<
    runErrorT (runStateT (runReaderT (unInfer f) ps) (progOverloads prog))

runInferProg :: Infer TypeEnv -> Prog -> IO Prog
runInferProg f prog = do
  (g,o) <- runInfer StageInfer (prog,[]) f
  return $ prog { progGlobalTypes = g, progOverloads = o }

-- |'rerunInfer' discards any extra function info computed during the extra inference.
rerunInfer :: Stage -> (Prog, InferStack) -> Infer a -> IO a
rerunInfer st ps f = fst =.< runInfer st ps f

instance ProgMonad Infer where
  getProg = fst =.< ask

debugInfer :: String -> Infer ()
debugInfer m = Infer $ ask >>= \(_,s) -> liftIO $ do
  putStrLn (concatMap (\f -> pshow (callFunction f) ++ ":") (reverse s) ++ ' ':m)


-- |Indicate a potentially recoverable substitution failure/type error that could be caught during overload resolution
typeError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a
typeError l m = throwError $ ErrorStack [] l (pretty m)

typeMismatch :: (Pretty a, Pretty b, MonadError TypeError m) => a -> String -> b -> m c
typeMismatch x op y = typeError noLoc $ pretty "type mismatch:" <+> quotes (pretty x) <+> pretty op <+> quotes (pretty y) <+> pretty "failed"

typeErrors :: (Pretty s, Pretty s', MonadError TypeError m) => SrcLoc -> s -> [(s',TypeError)] -> m a
typeErrors l m tel = typeError l $ nested' m $ vcat $ map (uncurry nested') tel

typeReError :: (Pretty s, MonadError TypeError m) => SrcLoc -> s -> m a -> m a
typeReError l m f = catchError f $ \te -> typeError l $ nested' m te
