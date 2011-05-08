{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances, GeneralizedNewtypeDeriving, PatternGuards #-}
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

stageNames :: [String]
stageNames =
    ["ast"
    ,"ir"
    ,"lir"
    ,"link"
    ,"infer"
    ,"exec"
    ]

instance Pretty Stage where
  pretty = pretty . s where
    s StageParse = "parse"
    s StageIr = "code"
    s StageLir = "lifting"
    s StageLink = "link"
    s StageInfer = "type"
    s StageExec = "runtime"

newtype Msg = Msg Doc
  deriving (Pretty)

instance Show Msg where
  showsPrec p (Msg m) = showsPrec p m

msg :: Pretty s => s -> Msg
msg = Msg . pretty

locMsg :: Pretty s => SrcLoc -> s -> Msg
locMsg l = msg . nestedPunct ':' l

stageMsg :: Pretty s => Stage -> SrcLoc -> s -> Msg
stageMsg st l m = locMsg l (st <+> "error" <:> m)

-- |To Err is human; to report anatine.
data Err = 
  Err Msg
  deriving (Typeable)

instance Show Err where
  showsPrec p (Err m) = showsPrec p m

instance Exception Err

stageExitval :: Stage -> Int
stageExitval StageExec = 3
stageExitval _ = 1

fatal :: Msg -> a
fatal = throw . Err

fatalIO :: MonadIO m => Msg -> m a
fatalIO = liftIO . throwIO . Err

dieStageErr :: Stage -> Err -> IO a
dieStageErr s e = die (stageExitval s) $ show e

isUnexpected :: SomeException -> Maybe SomeException
isUnexpected e | Just _ <- fromException e :: Maybe ExitCode = Nothing
             | otherwise = Just e

dieUnexpected :: Stage -> SomeException -> IO a
dieUnexpected s e = die 7 $ show (pretty s)++": internal error: "++show e

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
  { msgStack :: (CallStack a) -- ^ This should be in call order: outside to in
  , stackMsg :: Msg
  }

instance Pretty a => Pretty (StackMsg a) where
  pretty' (StackMsg s m) = s $$ m
