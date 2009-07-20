-- | Duck lexer

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-unused-matches #-}

module Lex where

import Var
import Token
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
  \{      { c (TokLC Nothing) }
  \}      { c (TokRC Nothing) }
  \;      { c (TokSemi Nothing) }
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

type AlexInput = ParseState

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = ps_prev

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar s = case ps_rest s of
  [] -> Nothing
  c:r -> Just (c, s
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

}
