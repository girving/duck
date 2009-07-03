{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards, TypeSynonymInstances #-}
-- Duck type inference monad

module InferMonad
  ( Infer
  , FunctionInfo
  , insertInfo
  , lookupInfo
  , typeError
  , withFrame
  , runInfer
  ) where

import Var
import Control.Monad.State hiding (guard)
import Control.Monad.Error hiding (guard)
import Util
import Type
import Ptrie (Ptrie')
import qualified Ptrie
import Data.Map (Map)
import qualified Data.Map as Map
import Pretty
import Text.PrettyPrint
import Control.Arrow hiding ((<+>))
import Control.Exception
import Callstack

-- Stores our current knowledge about the types of functions
type FunctionInfo = Map Var (Ptrie' Type Type)

type InferState = (Callstack Type, FunctionInfo)

data TypeError = TypeError (Callstack Type) String

instance Error TypeError where
  strMsg = TypeError []

newtype Infer a = Infer { unInfer :: StateT InferState (ErrorT TypeError IO) a }
  deriving (Monad, MonadIO, MonadError TypeError, MonadInterrupt)

insertInfo :: Var -> [Type] -> Type -> Infer ()
insertInfo f tl r = do
  -- liftIO (putStrLn ("recorded "++show (pretty f)++" "++show (prettylist tl)++" = "++show (pretty r)))
  (Infer . modify) (second (Map.alter (Ptrie.insert tl r) f))

lookupInfo :: Var -> [Type] -> Infer (Maybe Type)
lookupInfo f tl = Infer get >.= \ (_,info) ->
  case Ptrie.lookup tl (Map.lookup f info) of
    Nothing -> Nothing -- no match, type not yet inferred
    Just p | Just t <- Ptrie.unleaf' p -> Just t -- fully applied
    Just _ -> Just (TyClosure [(f,tl)]) -- partially applied

showError :: TypeError -> String
showError (TypeError stack msg) = showStack stack ++ "Type error: "++msg

makeTypeError :: String -> Infer TypeError
makeTypeError msg = Infer $ get >.= \ (s,_) -> TypeError s msg

typeError :: String -> Infer a
typeError msg = throwError =<< makeTypeError msg

withFrame :: Var -> [Type] -> Infer a -> Infer a
withFrame f args e =
  handleE (\ (e :: AsyncException) -> die . showError =<< makeTypeError (show e))
    (Infer $ do
      (s,_) <- get
      when (length s > 10) (unInfer $ typeError "stack overflow")
      modify (first ((f,args):))
      r <- unInfer e
      modify (first (const s))
      return r)

runInfer :: FunctionInfo -> Infer a -> IO (a, FunctionInfo)
runInfer info e = runErrorT (runStateT (unInfer e) ([], info) >.= second snd) >>= either (die . showError) return

-- Pretty printing

instance Pretty FunctionInfo where
  pretty info = vcat [pr f tl r | (f,p) <- Map.toList info, (tl,r) <- Ptrie.toList' p] where
    pr f tl r = pretty f <+> prettylist tl <+> equals <+> pretty r
