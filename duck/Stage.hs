{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances, GeneralizedNewtypeDeriving, PatternGuards, FlexibleInstances #-}
-- | Compilation top-level staging tools

module Stage
  ( Stage(..), stageNames
  -- * Error messages
  , msg, locMsg, stageMsg
  -- ** Raising errors
  , fatal, fatalIO
  -- ** Catching errors
  , runStage 
  -- * Stack traces
  , CallStack
  , CallFrame(..)
  , mapStackArgs
  , StackMsg(..)
  ) where

import Data.Typeable
import Control.Exception
import Control.Monad.Trans
import System.Exit

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
  | StageExec
  deriving (Eq, Ord, Enum, Bounded)

-- used for both arguments and printing; should be made more friendly at some point
stageNames :: [String]
stageNames =
    ["parse"
    ,"code"
    ,"lift"
    ,"link"
    ,"type"
    ,"runtime"
    ]

instance Pretty Stage where
  pretty = pretty . (stageNames !!) . fromEnum

-- |To Err is human; to report anatine.
newtype Msg = Msg Doc
  deriving (Pretty, Typeable)

instance Show Msg where
  showsPrec p (Msg m) = showsPrec p m

instance Exception Msg

msg :: Pretty s => s -> Msg
msg = Msg . pretty

locMsg :: Pretty s => SrcLoc -> s -> Msg
locMsg l = msg . nestedPunct ':' l

stageMsg :: Pretty s => Stage -> SrcLoc -> s -> Msg
stageMsg st l m = locMsg l (st <+> "error" <:> m)

stageExitval :: Stage -> Int
stageExitval StageExec = 3
stageExitval _ = 1

fatal :: Pretty s => s -> a
fatal = throw . Msg . pretty

fatalIO :: (MonadIO m, Pretty s) => s -> m a
fatalIO = liftIO . throwIO . Msg . pretty

dieStageErr :: Stage -> Msg -> IO a
dieStageErr s e = die (stageExitval s) $ show e

isUnexpected :: SomeException -> Maybe SomeException
isUnexpected e | Just _ <- fromException e :: Maybe ExitCode = Nothing
             | otherwise = Just e

dieUnexpected :: Stage -> SomeException -> IO a
dieUnexpected s e = die 7 $ pout s++": internal error: "++show e

runStage :: Stage -> IO a -> IO a
runStage s = handleJust isUnexpected (dieUnexpected s) . handle (dieStageErr s)

-- |Represents a single function call with the given type of arguments.
data CallFrame a = CallFrame
  { callFunction :: Var
  , callArgs :: [a]
  , callLoc :: SrcLoc
  }

type CallStack a = [CallFrame a]

instance Functor CallFrame where
  fmap f c = c { callArgs = map f (callArgs c) }

instance Pretty a => Pretty (CallStack a) where
  pretty' s = vcat $ map p s where
    p (CallFrame f args loc) = loc <:> "in" <+> prettyap f args <+> "..."

mapStackArgs :: (a -> b) -> CallStack a -> CallStack b
mapStackArgs f = map $ fmap f

data StackMsg a = StackMsg
  { msgStack :: CallStack a -- ^ This should be in call order: outside to in
  , stackMsg :: Msg
  }

instance Pretty a => Pretty (StackMsg a) where
  pretty' (StackMsg s m) = s $$ m
