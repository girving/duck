-- Duck lexer

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-unused-matches #-}

module Lex where

import Var
import ParseMonad
}

$white = [\ \n\r] -- No tabs!
$digit = 0-9
$lower = [a-z_]
$upper = [A-Z]
$alphanum = [a-zA-Z0-9_']

tokens :-

  $white+ ;
  \-\-.*  ;
  def     { c TokDef }
  data    { c TokData }
  over    { c TokOver }
  let     { c TokLet }
  in      { c TokIn }
  case    { c TokCase }
  of      { c TokOf }
  =       { c TokEq }
  \->     { c TokArrow }
  \+      { c TokPlus }
  \-      { c TokMinus }
  \*      { c TokTimes }
  \/      { c TokDiv }
  \(      { c TokLP }
  \)      { c TokRP }
  :       { c TokColon }
  \;      { c TokSep }
  \,      { c TokComma }
  _       { c TokAny }
  \\      { c TokLambda }
  \|      { c TokOr }
  $digit+ { v (TokInt . read) }
  $lower $alphanum* { v (TokVar . V) }
  $upper $alphanum* { v (TokCVar . V) }

{

type Action = ParseState -> Int -> P Token

c :: (SrcLoc -> Token) -> Action
c t s _ = return $ t (ps_loc s)

v :: (String -> SrcLoc -> Token) -> Action
v t s len = return $ t (take len (ps_rest s)) (ps_loc s)

-- Each action has type :: String -> Token

data Token
  = TokVar Var SrcLoc
  | TokCVar Var SrcLoc
  | TokInt Int SrcLoc
  | TokEq SrcLoc
  | TokPlus SrcLoc
  | TokMinus SrcLoc
  | TokTimes SrcLoc
  | TokDiv SrcLoc
  | TokLP SrcLoc
  | TokRP SrcLoc
  | TokSep SrcLoc
  | TokColon SrcLoc
  | TokComma SrcLoc
  | TokDef SrcLoc
  | TokLet SrcLoc
  | TokOver SrcLoc
  | TokData SrcLoc
  | TokIn SrcLoc
  | TokCase SrcLoc
  | TokOf SrcLoc
  | TokAny SrcLoc
  | TokLambda SrcLoc
  | TokArrow SrcLoc
  | TokOr SrcLoc
  | TokEOF

instance Show Token where
  show t = case t of
    TokVar (V v) _ -> v
    TokCVar (V v) _ -> v
    TokInt i _ -> show i
    TokDef _ -> "def"
    TokLet _ -> "let"
    TokOver _ -> "over"
    TokData _ -> "data"
    TokIn _ -> "in"
    TokCase _ -> "case"
    TokOf _ -> "of"
    TokEq _ -> "="
    TokPlus _ -> "+"
    TokMinus _ -> "-"
    TokTimes _ -> "*"
    TokDiv _ -> "/"
    TokLP _ -> "("
    TokRP _ -> ")"
    TokSep _ -> ";"
    TokColon _ -> ":"
    TokComma _ -> ","
    TokAny _ -> "_"
    TokLambda _ -> "\\"
    TokArrow _ -> "->"
    TokOr _ -> "|"
    TokEOF -> "<eof>"

type AlexInput = ParseState

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = ps_prev

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar s = case ps_rest s of
  [] -> Nothing
  c:r -> Just (c, ParseState
    { ps_loc = move (ps_loc s) c
    , ps_rest = r
    , ps_prev = c } )

lexer :: P Token
lexer = do
  s <- getState
  case alexScan s 0 of
    AlexEOF -> return TokEOF
    AlexError _ -> fail "lexical error"
    AlexSkip s' _ -> do
      setState s'
      lexer
    AlexToken s' len action -> do
      setState s'
      action s len

-- happy wants the lexer in continuation form
lexwrap :: (Token -> P a) -> P a
lexwrap cont = lexer >>= cont

}
