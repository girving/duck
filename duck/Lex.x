-- | Duck lexer

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-unused-matches -fno-warn-unused-binds #-}

module Lex 
  ( lexer
  ) where

import qualified Data.Char as Char
import Control.Monad.State.Class
import Numeric

import Util
import Var
import Token
import SrcLoc
import ParseMonad
import ParseOps
}

$white = [\ \n\r] -- No tabs!
$digit = 0-9
$lower = [a-z_]
$upper = [A-Z]
$alphanum = [a-zA-Z0-9_']
$symbol = [! \# \$ \% & \* \+ \. \\ \/ \< = > \? @ \^ \| \- \~ :]

@char  = [^\\] | \\ ( [\\abtnvfr\"\'] | \^[@-_] | [o0] [0-7]{1,3} | x [0-9a-fA-F]{1,2} )

tokens :-

\{\-       { c TokComment }
\-\}       { c TokCommentEnd }
<comment>. ;
<0>\-\-.*  ;

$white+    ;

<0> {
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
  \' @char \'       { v chr }
}

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

readsChr :: ReadS Char
readsChr ('\\':'0':s) = map (first Char.chr) $ readOct s
readsChr ('\\':'o':s) = map (first Char.chr) $ readOct s
readsChr ('\\':'x':s) = map (first Char.chr) $ readHex s
readsChr ('\\':'^':a:s) = [(Char.chr (Char.ord a - Char.ord '@'),s)]
readsChr ('\\':'a':s) = [('\a',s)]
readsChr ('\\':'b':s) = [('\b',s)]
readsChr ('\\':'t':s) = [('\t',s)]
readsChr ('\\':'n':s) = [('\n',s)]
readsChr ('\\':'v':s) = [('\v',s)]
readsChr ('\\':'f':s) = [('\f',s)]
readsChr ('\\':'r':s) = [('\r',s)]
readsChr ('\\':c:s) = [(c,s)]
readsChr ('\\':_) = []
readsChr (c:s) = [(c,s)]
readsChr [] = []

chr :: Action
chr ('\'':s) | [(c,"'")] <- readsChr s = TokChr c
chr s = error ("bad character: " ++ s) -- should not happen

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
  let mode = if null (ps_comment s) then 0 else comment
  case alexScan s mode of
    AlexEOF -> return $ Loc (ps_loc s) TokEOF
    AlexError _ -> fail "lexical error"
    AlexSkip s' _ -> do
      put s'
      lexer
    AlexToken s' len action -> do
      put s'
      return $ Loc (rangeLoc (ps_loc s) (ps_loc s')) $ action (take len (ps_rest s))

}
