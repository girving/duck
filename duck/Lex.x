-- | Duck lexer
-- vim:filetype=haskell

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-unused-matches -fno-warn-unused-binds #-}
{-# LANGUAGE PatternGuards #-}

module Lex 
  ( lexer
  ) where

import Control.Monad.State.Class
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BSC
import qualified Data.Char as Char
import Data.Word (Word8)
import Numeric

import Util
import SrcLoc
import Var
import Token
import ParseMonad
}

$white = [\ \t\n\r]
$digit = 0-9
$lower = [a-z_]
$upper = [A-Z]
$alphanum = [a-zA-Z0-9_']
$symbol = [! \# \$ \% & \* \+ \. \\ \/ \< = > \? @ \^ \| \- \~ :]

@char  = [^\\] | \\ ( [\\abtnvfr\"\'] | \^[@-_] | [o0] [0-7]{1,3} | x [0-9a-fA-F]{1,2} )
-- fix for broken syntax highlighting: "

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
  data    { c TokData }
  let     { c (TokLet False) }
  slet    { c (TokLet True) }
  in      { c TokIn }
  case    { c (TokCase False) }
  scase   { c (TokCase True) }
  of      { c TokOf }
  if      { c (TokIf False) }
  sif     { c (TokIf True) }
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
  \" @char* \"	    { v str }
-- and another: "
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
sym "\\" = TokGroup
sym "-" = TokMinus
sym s@(':':_) = TokCSym (V s)
sym s = TokSym (V s)

readsChar :: ReadS Char
readsChar ('\\':'0':s) = map (first Char.chr) $ readOct s
readsChar ('\\':'o':s) = map (first Char.chr) $ readOct s
readsChar ('\\':'x':s) = map (first Char.chr) $ readHex s
readsChar ('\\':'^':a:s) = [(Char.chr (ord a - ord '@'),s)]
readsChar ('\\':'a':s) = [('\a',s)]
readsChar ('\\':'b':s) = [('\b',s)]
readsChar ('\\':'t':s) = [('\t',s)]
readsChar ('\\':'n':s) = [('\n',s)]
readsChar ('\\':'v':s) = [('\v',s)]
readsChar ('\\':'f':s) = [('\f',s)]
readsChar ('\\':'r':s) = [('\r',s)]
readsChar ('\\':c:s) = [(c,s)]
readsChar ('\\':_) = []
readsChar (c:s) = [(c,s)]
readsChar [] = []

chr :: Action
chr ~('\'':s) | ~[(c,"'")] <- readsChar s = TokChar c

str :: Action
str ~('"':s) = TokString $ rstr s where
  rstr ['"'] = []
  rstr s | ~[(c,s')] <- readsChar s = c : rstr s'

type AlexInput = ParseState

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = ps_prev

alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte p = do
  (b, r) <- BS.uncons (ps_input p)
  let c = B.w2c b
  return (b, p
    { ps_loc = incrLoc (ps_loc p) c
    , ps_prev = c
    , ps_input = r
    })

lexer :: P (Loc Token)
lexer = do
  s <- get
  let mode = case ps_layout s of { Context Comment _ _ : _ -> comment ; _ -> 0 }
  case alexScan s mode of
    AlexEOF -> return $ L (ps_loc s) TokEOF
    AlexError s' -> psError s' "lexical error"
    AlexSkip s' _ -> do
      put s'
      lexer
    AlexToken s' len action -> do
      put s'
      return $ L (rangeLoc (ps_loc s) (ps_loc s')) $ action $ 
        -- XXX: breaks non-latin1 encoding
        BSC.unpack $ BS.take (fromIntegral len) $ ps_input s

}
