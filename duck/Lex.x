-- Duck lexer

{
{-# OPTIONS_GHC -w #-}

module Lex where

import Ast
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z_]
$alphanum = [a-zA-Z0-9_']

tokens :-

  $white+ ;
  \#.*    ;
  def     { c TokDef }
  let     { c TokLet }
  in      { c TokIn }
  =       { c TokEq }
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
  $digit+ { TokInt . read }
  $alpha $alphanum* { TokVar }

{

c = const

-- Each action has type :: String -> Token

data Token
  = TokVar Var
  | TokInt Int
  | TokEq
  | TokPlus
  | TokMinus
  | TokTimes
  | TokDiv
  | TokLP
  | TokRP
  | TokSep
  | TokColon
  | TokComma
  | TokDef
  | TokLet
  | TokIn
  | TokAny

instance Show Token where
  show t = case t of
    TokVar v -> v
    TokInt i -> show i
    TokDef -> "def"
    TokLet -> "let"
    TokIn -> "in"
    TokEq -> "="
    TokPlus -> "+"
    TokMinus -> "-"
    TokTimes -> "*"
    TokDiv -> "/"
    TokLP -> "("
    TokRP -> ")"
    TokSep -> ";"
    TokColon -> ":"
    TokComma -> ","
    TokAny -> "_"

lexer = alexScanTokens
}
