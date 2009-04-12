-- Duck lexer

module Lex where

import Data.Char
import Ast

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

lexer :: String -> [Token]

lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isAlpha c = lexVar (c:cs)
  | isDigit c = lexInt (c:cs)
lexer ('=':cs) = TokEq : lexer cs
lexer ('+':cs) = TokPlus : lexer cs
lexer ('-':cs) = TokMinus : lexer cs
lexer ('*':cs) = TokTimes : lexer cs
lexer ('/':cs) = TokDiv : lexer cs
lexer ('(':cs) = TokLP : lexer cs
lexer (')':cs) = TokRP : lexer cs
lexer (':':cs) = TokColon : lexer cs
lexer (';':cs) = TokSep : lexer cs
lexer (',':cs) = TokComma : lexer cs
lexer _ = error "Lexer error"

lexInt cs = TokInt (read num) : lexer rest
  where (num,rest) = span isDigit cs

lexVar cs = token : lexer rest where
  (var,rest) = span isAlpha cs
  token = case var of
    "def" -> TokDef
    _ -> TokVar var

instance Show Token where
  show t = case t of
    TokVar v -> v
    TokInt i -> show i
    TokDef -> "def"
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
