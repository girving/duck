-- Duck Lexer/Parser Monads

module ParseMonad where

-- Simple parser monad lifted from a combination of a happy example and Language.Haskell
-- This accomplishes three things:
--   1. It passes the input string around.
--   2. It passes the current line and column numbers around.
--   3. It deals with success/failure.

import Util

data SrcLoc = SrcLoc !Int !Int -- line and column numbers

instance Show SrcLoc where
  show (SrcLoc line col) = show line ++ ':': show col

start :: SrcLoc
start = SrcLoc 1 1

move :: SrcLoc -> Char -> SrcLoc
move (SrcLoc l _) '\n' = SrcLoc (l+1) 1
move (SrcLoc l c) _    = SrcLoc l (c+1)

data ParseResult a
  = ParseOk ParseState a
  | ParseFail ParseError

type ParseError = (SrcLoc, String)

data ParseState = ParseState {
  ps_loc  :: !SrcLoc, -- position at current input location
  ps_rest :: String,  -- the current input
  ps_prev :: !Char }  -- the character before the input

newtype P a = P { unP :: ParseState -> ParseResult a }

instance Monad P where
  m >>= k = P $ \s -> case (unP m) s of
    ParseOk s a -> (unP (k a)) s
    ParseFail e -> ParseFail e

  return a = P $ \s -> ParseOk s a

  fail msg = P $ \s -> ParseFail (ps_loc s, msg ++ case ps_rest s of
    [] -> " at end of file"
    c:_ -> " before " ++ show c)

runP :: P a -> String -> IO a
runP parser input =
  case (unP parser) (ParseState start input '\n') of 
    ParseOk _ a -> return a
    ParseFail (l, s) -> die (show l ++ ": " ++ s)

getState :: P ParseState
getState = P $ \s -> ParseOk s s

setState :: ParseState -> P ()
setState s = P $ \_ -> ParseOk s ()
