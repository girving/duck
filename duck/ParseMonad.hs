{-# LANGUAGE MultiParamTypeClasses #-}
-- Duck Lexer/Parser Monads

module ParseMonad 
  ( SrcLoc
  , move
  , P
  , ParseState(..)
  , parseFile
  , runP
  , get, put
  ) where

-- Simple parser monad lifted from a combination of a happy example and Language.Haskell
-- This accomplishes three things:
--   1. It passes the input string around.
--   2. It passes the current line and column numbers around.
--   3. It deals with success/failure.

import Util
import Control.Monad.State.Class
import Control.Monad.Trans
import Var
import System.FilePath
import Data.Map (Map)
import qualified Data.Map as Map

data SrcLoc = SrcLoc String !Int !Int -- filename, line and column numbers

instance Show SrcLoc where
  show (SrcLoc file line col) = file ++ ':' : show line ++ ':': show col

start :: String -> SrcLoc
start file = SrcLoc file 1 1

move :: SrcLoc -> Char -> SrcLoc
move (SrcLoc f l _) '\n' = SrcLoc f (l+1) 1
move (SrcLoc f l c) _    = SrcLoc f l (c+1)

data ParseResult a
  = ParseOk ParseState a
  | ParseFail ParseError

type ParseError = (SrcLoc, String)

data ParseState = ParseState {
  ps_loc  :: !SrcLoc, -- position at current input location
  ps_rest :: String,  -- the current input
  ps_prev :: !Char,   -- the character before the input
  ps_prec :: Map Var PrecFix } -- precedence and associativity of binary operators

newtype P a = P { unP :: ParseState -> IO (ParseResult a) }

instance Monad P where
  m >>= k = P $ \s -> (unP m) s >>= \r ->
    case r of
      ParseOk s a -> (unP (k a)) s
      ParseFail e -> return (ParseFail e)

  return a = P $ \s -> return (ParseOk s a)

  fail msg = P $ \s -> return $ ParseFail (ps_loc s, msg ++ case ps_rest s of
    [] -> " at end of file"
    c:_ -> " before " ++ show c)

instance MonadIO P where
  liftIO a = P $ \s -> a >>= \r -> return (ParseOk s r)

parseString :: P a -> String -> String -> P a
parseString parse file input = do
  s <- get
  put (ParseState (start file) input '\n' Map.empty)
  r <- parse
  s' <- get
  put (s { ps_prec = ps_prec s' }) -- precedence declarations should carry through
  return r

parseFile :: P a -> String -> P a
parseFile parse file = do
  s <- get
  let SrcLoc current _ _ = ps_loc s
      dir = dropFileName current
  input <- liftIO $ readFile (dir </> file++".duck")
  parseString parse file input
 
runP :: P a -> String -> String -> IO a
runP parse file input = do
  (unP parse) (ParseState (start file) input '\n' Map.empty) >>= \r ->
    case r of
      ParseOk _ a -> return a
      ParseFail (l, s) -> die (show l ++ ": " ++ s)

instance MonadState ParseState P where
  get = P $ \s -> return $ ParseOk s s

  put s = P $ \_ -> return $ ParseOk s ()
