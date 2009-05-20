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
$symbol = [! \# \$ \% & \* \+ \. \\ \/ \< = > \? @ \^ \| \- \~ :]

tokens :-

  $white+ ;
  \-\-.*  ;
  import  { c TokImport }
  infixl  { c (TokInfix Leftfix) }
  infixr  { c (TokInfix Rightfix) }
  infix   { c (TokInfix Nonfix) }
  def     { c TokDef }
  data    { c TokData }
  over    { c TokOver }
  let     { c TokLet }
  in      { c TokIn }
  case    { c TokCase }
  of      { c TokOf }
  \(      { c TokLP }
  \)      { c TokRP }
  \;      { c TokSep }
  \,      { c TokComma }
  _       { c TokAny }
  $digit+ { v (TokInt . read) }
  $lower $alphanum* { v (TokVar . V) }
  $upper $alphanum* { v (TokCVar . V) }
  $symbol+          { v sym }

{

type Action = ParseState -> Int -> P Token

c :: (SrcLoc -> Token) -> Action
c t s _ = return $ t (ps_loc s)

v :: (String -> SrcLoc -> Token) -> Action
v t s len = return $ t (take len (ps_rest s)) (ps_loc s)

sym :: String -> SrcLoc -> Token
sym "=" = TokEq
sym "->" = TokArrow
sym "::" = TokDColon
sym "\\" = TokLambda
sym "|" = TokOr
sym s@(':':_) = TokCSym (V s)
sym s = TokSym (V s)

-- Each action has type :: String -> Token

data Token
  = TokVar Var SrcLoc
  | TokCVar Var SrcLoc
  | TokSym Var SrcLoc
  | TokCSym Var SrcLoc
  | TokInt Int SrcLoc
  | TokEq SrcLoc
  | TokLP SrcLoc
  | TokRP SrcLoc
  | TokSep SrcLoc
  | TokDColon SrcLoc
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
  | TokImport SrcLoc
  | TokInfix Fixity SrcLoc
  | TokEOF

instance Show Token where
  show t = case t of
    TokVar (V v) _ -> v
    TokCVar (V v) _ -> v
    TokSym (V v) _ -> v
    TokCSym (V v) _ -> v
    TokInt i _ -> show i
    TokDef _ -> "def"
    TokLet _ -> "let"
    TokOver _ -> "over"
    TokData _ -> "data"
    TokIn _ -> "in"
    TokCase _ -> "case"
    TokOf _ -> "of"
    TokImport _ -> "import"
    TokInfix Leftfix _ -> "infixl"
    TokInfix Rightfix _ -> "infixr"
    TokInfix Nonfix _ -> "infix"
    TokEq _ -> "="
    TokLP _ -> "("
    TokRP _ -> ")"
    TokSep _ -> ";"
    TokDColon _ -> ":"
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
    , ps_prev = c
    , ps_prec = ps_prec s } )

lexer :: P Token
lexer = do
  s <- get
  case alexScan s 0 of
    AlexEOF -> return TokEOF
    AlexError _ -> fail "lexical error"
    AlexSkip s' _ -> do
      put s'
      lexer
    AlexToken s' len action -> do
      put s'
      action s len

-- happy wants the lexer in continuation form
lexwrap :: (Token -> P a) -> P a
lexwrap cont = lexer >>= cont

}
