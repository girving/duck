{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleContexts, DeriveDataTypeable #-}
-- | Duck Lexer/Parser Monads
--
-- Simple parser monad lifted from a combination of a happy example and Language.Haskell
-- This accomplishes three things:
--
-- (1) It passes the input string around.
--
-- (2) It passes the current line and column numbers around.
--
-- (3) It deals with success/failure.


module ParseMonad 
  ( P
  , ParseState(..)
  , runP
  , parseError , psError
  , Context(..)
  ) where

import Prelude hiding (catch)
import Control.Monad.State

import Pretty
import SrcLoc
import Stage

-- |Layout contexts can be either be explicit when started by a literal '{' token
-- or implicit when the '{' is left out.  The full source location is included
-- for error reporting purposes.
data Context =
    Explicit SrcLoc
  | Implicit SrcLoc Int

data ParseState = ParseState 
  { ps_loc    :: !SrcLoc   -- ^ position at current input location
  , ps_rest   :: String    -- ^ the current input
  , ps_prev   :: !Char     -- ^ the character before the input
  , ps_layout :: [Context] -- ^ stack of layout contexts
  , ps_start  :: !Bool     -- ^ True if we're at the start of a new layout context (after SOF or 'of')
  , ps_last   :: SrcLoc    -- ^ the location of the last token processed by layout (in order to detect new lines)
  , ps_comment :: [SrcLoc] -- ^ start of current multiline comments, so length is nesting level
  }

type P a = State ParseState a

parseError :: Pretty s => SrcLoc -> s -> a
parseError l = fatal . stageMsg StageParse l

psError :: Pretty s => ParseState -> s -> a
psError s = parseError (ps_loc s)

runP :: P a -> String -> String -> a
runP parse file input = r where
  (r,_) = runState parse $ ParseState
    { ps_loc = (startLoc file)
    , ps_rest = input
    , ps_prev = '\n'
    , ps_layout = []
    , ps_start = True
    , ps_last = noLoc
    , ps_comment = []
    }
