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
  , ContextType(..), Context(..)
  ) where

import Prelude hiding (catch)
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS

import Pretty
import SrcLoc
import Stage
import Token

-- |Layout contexts can be either be explicit when started by a literal '{' token
-- or implicit when the '{' is left out.
data ContextType
  = Outside -- ^ Virtual type for having no context
  | Explicit
  | ImplicitBlock -- ^ Inserts delimiters
  | ImplicitLine -- ^ Only closes
  | Comment
data Context = Context 
  { contextType :: !ContextType
  , contextLead :: Loc Token -- ^ token which opened this contex
  , contextCol :: !Int
  }

data ParseState = ParseState 
  { ps_loc    :: !SrcLoc   -- ^ position at current input location
  , ps_prev   :: !Char     -- ^ the character before the input
  , ps_input  :: !BS.ByteString -- ^ the current input
  , ps_layout :: [Context] -- ^ stack of layout contexts
  , ps_last   :: Loc Token -- ^ the last token processed by layout (in order to detect new lines)
  }

type P a = State ParseState a

parseError :: Pretty s => SrcLoc -> s -> a
parseError l = fatal . stageMsg StageParse l

psError :: Pretty s => ParseState -> s -> a
psError s = parseError (ps_loc s)

runP :: P a -> String -> BS.ByteString -> a
runP parse file input = r where
  (r,_) = runState parse ParseState
    { ps_loc = loc
    , ps_prev = '\n'
    , ps_input = input
    , ps_layout = []
    , ps_last = L loc TokSOF
    } where loc = startLoc file
