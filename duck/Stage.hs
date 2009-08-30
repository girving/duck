{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances #-}
-- | Compilation top-level staging tools

module Stage
  ( Stage(..)
  , stageError, stageErrorIO
  , catchFatal
  -- * Stack traces
  , CallStack
  , CallFrame(..)
  , mapStackArgs
  , ErrorStack(..)
  ) where

import Data.Typeable
import Control.Exception
import Control.Monad.Trans

import Util
import Var
import Pretty
import SrcLoc

data Stage 
  = StageParse
  | StageIr
  | StageLir
  | StageLink
  | StageInfer
  | StageEnv
  | StageExec
  deriving (Eq, Ord, Enum, Bounded)

instance TextEnum Stage where
  enumTexts = zip allOf
    ["parse"
    ,"ir"
    ,"lir"
    ,"link"
    ,"infer"
    ,"env"
    ,"exec"
    ]

instance Show Stage where show = showEnum
instance Read Stage where readsPrec _ = readsEnum
instance Pretty Stage where pretty = pretty . show

data StageError = StageError
  { errStage :: Stage -- ^ Currently the part of the code that generated the error, but perhaps should be removed, and represent when the error occured
  , _errLoc :: SrcLoc
  , _errMsg :: Doc
  } deriving (Typeable)

instance Show StageError where
  show (StageError _ l s) = show (nested' l s)

instance Exception StageError

instance Functor CallFrame where
  fmap f c = c { callArgs = map f (callArgs c) }

stageExitval :: Stage -> Int
stageExitval StageExec = 3
stageExitval _ = 1

stageError :: Pretty s => Stage -> SrcLoc -> s -> a
stageError p l s = throw $ StageError p l $ pretty s

stageErrorIO :: (MonadIO m, Pretty s) => Stage -> SrcLoc -> s -> m a
stageErrorIO p l s = liftIO $ throwIO $ StageError p l $ pretty s

errorFatal :: StageError -> IO a
errorFatal e = dieWith (stageExitval (errStage e)) $ show e

catchFatal :: IO a -> IO a
catchFatal = handle errorFatal

-- |Represents a single function call with the given type of arguments.
data CallFrame a = CallFrame
  { callFunction :: Var
  , callArgs :: [a]
  , callLoc :: SrcLoc
  }

type CallStack a = [CallFrame a]

instance Pretty a => Pretty (CallStack a) where
  pretty s = vcat $ map p s where
    p (CallFrame f args loc) = mapPretty (<> pretty ':') loc <+> pretty "in" <+> pretty f <+> prettylist args <+> pretty "..."

mapStackArgs :: (a -> b) -> CallStack a -> CallStack b
mapStackArgs f = map $ fmap f

data ErrorStack a = ErrorStack
  { errStack :: CallStack a
  , errLoc :: SrcLoc
  , errMsg :: Doc
  }

instance Pretty a => Pretty (ErrorStack a) where
  pretty (ErrorStack s l m) = pretty s $$ nested' l m
