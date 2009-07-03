{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleContexts, DeriveDataTypeable #-}
-- Duck Lexer/Parser Monads

module ParseMonad 
  ( P
  , ParseState(..)
  , ParseError(..)
  , parseFile
  , runP
  , parseError
  , parseTry
  , get, put
  , ParseMonad
  ) where

-- Simple parser monad lifted from a combination of a happy example and Language.Haskell
-- This accomplishes three things:
--   1. It passes the input string around.
--   2. It passes the current line and column numbers around.
--   3. It deals with success/failure.

import Prelude hiding (catch)
import Util
import Control.Monad.State.Class
import Control.Monad.Trans
import qualified Control.Monad.Error.Class as MError
import SrcLoc
import System.FilePath
import Data.Typeable (Typeable)
import Data.Monoid
import Control.Exception (Exception, evaluate, catch, throw)

data ParseResult a
  = ParseOk ParseState a
  | ParseFail ParseError

data ParseError = ParseError 
  { errLoc :: SrcLoc
  , errMsg :: String
  } deriving (Typeable)

data ParseState = ParseState 
  { ps_loc  :: !SrcLoc -- position at current input location
  , ps_rest :: String  -- the current input
  , ps_prev :: !Char   -- the character before the input
  }

newtype P a = P { unP :: ParseState -> IO (ParseResult a) }

class (MonadState ParseState m, MError.MonadError ParseError m) => ParseMonad m

instance Show ParseError where
  show (ParseError l s) = show l ++ ':' : s

instance Exception ParseError

psError :: ParseState -> String -> ParseError
psError s msg = ParseError (ps_loc s) $ msg ++ case ps_rest s of
    [] -> " at end of file"
    c:_ -> " before " ++ show c

instance Monad P where
  m >>= k = P $ \s -> (unP m) s >>= \r ->
    case r of
      ParseOk s a -> (unP (k a)) s
      ParseFail e -> return (ParseFail e)

  return a = P $ \s -> return (ParseOk s a)

  fail msg = P $ \s -> return $ ParseFail $ psError s msg

instance MonadIO P where
  liftIO a = P $ \s -> a >>= \r -> return (ParseOk s r)

instance MError.Error ParseError where
  strMsg s = ParseError mempty s

instance MError.MonadError ParseError P where
  throwError e = P $ \_ -> return $ ParseFail e

  catchError m f = P $ \s -> (unP m) s >>= \r ->
    case r of
      ParseOk _ _ -> return r
      ParseFail e -> (unP (f e)) s

parseString :: P a -> String -> String -> P a
parseString parse file input = do
  s <- get
  put (ParseState (startLoc file) input '\n')
  r <- parse
  put s
  return r

parseFile :: P a -> String -> P a
parseFile parse file = do
  s <- get
  let dir = dropFileName $ srcFile $ ps_loc s
  input <- liftIO $ readFile (dir </> file++".duck")
  parseString parse file input
 
runP :: P a -> String -> String -> IO a
runP parse file input = do
  (unP parse) (ParseState (startLoc file) input '\n') >>= \r ->
    case r of
      ParseOk _ a -> return a
      ParseFail e -> die (show e)

instance MonadState ParseState P where
  get = P $ \s -> return $ ParseOk s s

  put s = P $ \_ -> return $ ParseOk s ()

parseError :: String -> a
parseError s = throw (MError.strMsg s :: ParseError)

parseTry :: a -> P a
parseTry x = P $ \s ->
  catch (ParseOk s =.< evaluate x) $ \(ParseError l m) -> return (ParseFail (ParseError (mappend l (ps_loc s)) m))

instance ParseMonad P
