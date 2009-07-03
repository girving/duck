-- Duck lexer

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
sym "-" = TokMinus
sym s@(':':_) = TokCSym (V s)
sym s = TokSym (V s)

-- Each action has type :: String -> Token

data Token
  = TokVar { tokVar :: Var, tokLoc :: SrcLoc }
  | TokCVar { tokCVar :: Var, tokLoc :: SrcLoc }
  | TokSym { tokSym :: Var, tokLok :: SrcLoc }
  | TokCSym { tokCSym :: Var, tokLok :: SrcLoc }
  | TokInt { tokInt :: Int, tokLok :: SrcLoc }
  | TokEq { tokLok :: SrcLoc }
  | TokLP { tokLok :: SrcLoc }
  | TokRP { tokLok :: SrcLoc }
  | TokLB { tokLok :: SrcLoc }
  | TokRB { tokLok :: SrcLoc }
  | TokSep { tokLok :: SrcLoc }
  | TokDColon { tokLok :: SrcLoc }
  | TokComma { tokLok :: SrcLoc }
  | TokDef { tokLok :: SrcLoc }
  | TokLet { tokLok :: SrcLoc }
  | TokOver { tokLok :: SrcLoc }
  | TokData { tokLok :: SrcLoc }
  | TokIn { tokLok :: SrcLoc }
  | TokCase { tokLok :: SrcLoc }
  | TokOf { tokLok :: SrcLoc }
  | TokIf { tokLok :: SrcLoc }
  | TokThen { tokLok :: SrcLoc }
  | TokElse { tokLok :: SrcLoc }
  | TokAny { tokLok :: SrcLoc }
  | TokLambda { tokLok :: SrcLoc }
  | TokArrow { tokLok :: SrcLoc }
  | TokOr { tokLok :: SrcLoc }
  | TokMinus { tokLok :: SrcLoc }
  | TokImport { tokLok :: SrcLoc }
  | TokInfix { tokFix :: Fixity, tokLok :: SrcLoc }
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
    TokIf _ -> "if"
    TokThen _ -> "then"
    TokElse _ -> "else"
    TokImport _ -> "import"
    TokInfix LeftFix _ -> "infixl"
    TokInfix RightFix _ -> "infixr"
    TokInfix NonFix _ -> "infix"
    TokEq _ -> "="
    TokLP _ -> "("
    TokRP _ -> ")"
    TokLB _ -> "["
    TokRB _ -> "]"
    TokSep _ -> ";"
    TokDColon _ -> ":"
    TokComma _ -> ","
    TokAny _ -> "_"
    TokLambda _ -> "\\"
    TokArrow _ -> "->"
    TokOr _ -> "|"
    TokMinus _ -> "-"
    TokEOF -> "<eof>"

type AlexInput = ParseState

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = ps_prev

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar s = case ps_rest s of
  [] -> Nothing
  c:r -> Just (c, ParseState
    { ps_loc = moveLoc (ps_loc s) c
    , ps_rest = r
    , ps_prev = c
    } )

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
