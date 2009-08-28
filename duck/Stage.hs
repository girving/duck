{-# LANGUAGE DeriveDataTypeable #-}
-- | Compilation top-level staging tools

module Stage
  ( Stage(..)
  , stageError, stageErrorIO
  , catchFatal
  ) where

import Data.Typeable
import Control.Exception
import Control.Monad.Trans

import Util
import Pretty
import SrcLoc

data Stage 
  = StageParse
  | StageIr
  | StageLir
  | StageLink
  | StageInfer
  | StageEnv
  deriving (Eq, Ord, Enum, Bounded)

instance TextEnum Stage where
  enumTexts = zip allOf
    ["parse"
    ,"ir"
    ,"lir"
    ,"link"
    ,"infer"
    ,"env"
    ]

instance Show Stage where show = showEnum
instance Read Stage where readsPrec _ = readsEnum
instance Pretty Stage where pretty = pretty . show

data StageError = StageError
  { _errStage :: Stage
  , _errLoc :: SrcLoc
  , _errStr :: String
  } deriving (Typeable)

instance Show StageError where
  showsPrec _ (StageError _ l s)
    | hasLoc l = shows l . (++) ": " . (++) s
    | otherwise = (++) s

instance Exception StageError

stageError :: Stage -> SrcLoc -> String -> a
stageError p l s = throw $ StageError p l s

stageErrorIO :: MonadIO m => Stage -> SrcLoc -> String -> m a
stageErrorIO p l s = liftIO $ throwIO $ StageError p l s

errorFatal :: StageError -> IO a
errorFatal = die . show

catchFatal :: IO a -> IO a
catchFatal = handle errorFatal
