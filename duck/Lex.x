-- | Duck lexer

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-unused-matches #-}

module Lex where

import Var
import SrcLoc
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
  infixl  { c (TokInfix LeftFix) }
  infixr  { c (TokInfix RightFix) }
  infix   { c (TokInfix NonFix) }
  def     { c TokDef }
  data    { c TokData }
  over    { c TokOver }
  let     { c TokLet }
  in      { c TokIn }
  case    { c TokCase }
  of      { c TokOf }
  if      { c TokIf }
  then    { c TokThen }
  else    { c TokElse }
  \(      { c TokLP }
  \)      { c TokRP }
  \[      { c TokLB }
  \]      { c TokRB }
  \;      { c TokSep }
  \,      { c TokComma }
  _       { c TokAny }
  $digit+ { v (TokInt . read) }
  $lower $alphanum* { v (TokVar . V) }
  $upper $alphanum* { v (TokCVar . V) }
  $symbol+          { v sym }

{

type Action = String -> Token

c :: Token -> Action
c = const

v :: (String -> Token) -> Action
v = id

sym :: String -> Token
sym "=" = TokEq
sym "->" = TokArrow
sym "::" = TokDColon
sym "\\" = TokLambda
sym "|" = TokOr
sym "-" = TokMinus
sym s@(':':_) = TokCSym (V s)
sym s = TokSym (V s)

-- Each action has type :: String -> Token

data Token
  = TokVar { tokVar :: Var }
  | TokCVar { tokVar :: Var }
  | TokSym { tokVar :: Var }
  | TokCSym { tokVar :: Var }
  | TokInt { tokInt :: Int }
  | TokEq
  | TokLP
  | TokRP
  | TokLB
  | TokRB
  | TokSep
  | TokDColon
  | TokComma
  | TokDef
  | TokLet
  | TokOver
  | TokData
  | TokIn
  | TokCase
  | TokOf
  | TokIf
  | TokThen
  | TokElse
  | TokAny
  | TokLambda
  | TokArrow
  | TokOr
  | TokMinus
  | TokImport
  | TokInfix { tokFix :: Fixity }
  | TokEOF

instance Show Token where
  show t = case t of
    TokVar (V v) -> v
    TokCVar (V v) -> v
    TokSym (V v) -> v
    TokCSym (V v) -> v
    TokInt i -> show i
    TokDef -> "def"
    TokLet -> "let"
    TokOver -> "over"
    TokData -> "data"
    TokIn -> "in"
    TokCase -> "case"
    TokOf -> "of"
    TokIf -> "if"
    TokThen -> "then"
    TokElse -> "else"
    TokImport -> "import"
    TokInfix LeftFix -> "infixl"
    TokInfix RightFix -> "infixr"
    TokInfix NonFix -> "infix"
    TokEq -> "="
    TokLP -> "("
    TokRP -> ")"
    TokLB -> "["
    TokRB -> "]"
    TokSep -> ";"
    TokDColon -> ":"
    TokComma -> ","
    TokAny -> "_"
    TokLambda -> "\\"
    TokArrow -> "->"
    TokOr -> "|"
    TokMinus -> "-"
    TokEOF -> "<eof>"

type AlexInput = ParseState

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = ps_prev

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar s = case ps_rest s of
  [] -> Nothing
  c:r -> Just (c, ParseState
    { ps_loc = incrLoc (ps_loc s) c
    , ps_rest = r
    , ps_prev = c
    } )

lexer :: P (Loc Token)
lexer = do
  s <- get
  case alexScan s 0 of
    AlexEOF -> return $ Loc (ps_loc s) TokEOF
    AlexError _ -> fail "lexical error"
    AlexSkip s' _ -> do
      put s'
      lexer
    AlexToken s' len action -> do
      put s'
      return $ Loc (srcRng (ps_loc s) (ps_loc s')) $ action (take len (ps_rest s))

-- happy wants the lexer in continuation form
lexwrap :: (Loc Token -> P a) -> P a
lexwrap cont = lexer >>= cont

}
