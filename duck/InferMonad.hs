{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ScopedTypeVariables, Rank2Types, PatternGuards, TypeSynonymInstances #-}
-- Duck type inference monad

module InferMonad
  ( Infer
  , insertInfo
  , lookupInfo
  , typeError
  , withFrame
  , runInfer
  ) where

import Var
import Control.Monad.State hiding (guard)
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

type Callstack = [(Var, [Type])]

-- Stores our current knowledge about the types of functions
type FunctionInfo = Map Var (Ptrie' Type Type)

newtype Infer a = Infer { unInfer :: (StateT (Callstack, FunctionInfo) IO a) }
  deriving (Monad, MonadIO)

insertInfo :: Var -> [Type] -> Type -> Infer ()
insertInfo f tl r = do
  -- liftIO (putStrLn ("recorded "++show (pretty f)++" "++show (prettylist tl)++" = "++show (pretty r)))
  (Infer . modify) (second (Map.alter (Ptrie.insert tl r) f))

lookupInfo :: Var -> [Type] -> Infer (Maybe Type)
lookupInfo f tl = Infer get >.= \ (_,info) ->
  case Ptrie.lookup tl (Map.lookup f info) of
    Nothing -> Nothing -- no match, type not yet inferred
    Just p | Just t <- Ptrie.unleaf' p -> Just t -- fully applied
    Just _ -> Just (TyClosure f tl) -- partially applied

showStack :: Callstack -> String
showStack s = unlines (h : reverse (map p s)) where
  h = "Traceback (most recent call last):"
  p (f,args) = "  in "++show (pretty f)++' ' : show (prettylist args)

typeError :: String -> Infer a
typeError msg = Infer $ get >>= \ (s,_) ->
  liftIO (die (showStack s ++ "Type error: "++msg))

handleE :: Exception e => (forall a. e -> Infer a) -> Infer b -> Infer b
handleE h e = Infer (do
  s <- get
  mapStateT (handle (\e -> evalStateT (unInfer (h e)) s)) (unInfer e))

withFrame :: Var -> [Type] -> Infer a -> Infer a
withFrame f args e =
  handleE (\ (e :: AsyncException) -> typeError (show e))
    (Infer $ do
      (s,_) <- get
      when (length s > 10) (unInfer $ typeError "stack overflow")
      modify (first ((f,args):))
      r <- unInfer e
      modify (first (const s))
      return r)

runInfer :: Infer a -> IO (a, FunctionInfo)
runInfer e = runStateT (unInfer e) ([], Map.empty) >.= \ (x,(_,i)) -> (x,i)

-- Pretty printing

instance Pretty FunctionInfo where
  pretty info = vcat [pr f tl r | (f,p) <- Map.toList info, (tl,r) <- Ptrie.toList' p] where
    pr f tl r = pretty f <+> prettylist tl <+> equals <+> pretty r
