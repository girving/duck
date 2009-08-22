{-# LANGUAGE DeriveDataTypeable #-}
-- | Compilation top-level staging tools

module Stage
  ( Stage(..)
  , StageError
  , stageError
  , catchFatal
  ) where

import Data.Typeable
import Control.Exception
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
  showsPrec _ (StageError p l s) = shows p . (:) ':' . shows l . (++) ": " . (++) s

instance Exception StageError

stageError :: Stage -> SrcLoc -> String -> a
stageError p l s = throw $ StageError p l s

errorFatal :: StageError -> IO a
errorFatal = die . show

catchFatal :: IO a -> IO a
catchFatal = handle errorFatal
