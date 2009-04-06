-- Duck parser

{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-overlapping-patterns #-}

module Parse (lex, parse) where

import Lex
import Ast

}

%name parse
%tokentype { Token }
%error { parseError }

%token
  var { TokVar $$ }
  int { TokInt $$ }
  ';' { TokSep }
  '=' { TokEq }
  '+' { TokPlus }
  '-' { TokMinus }
  '*' { TokTimes }
  '/' { TokDiv }
  '(' { TokLP }
  ')' { TokRP }

%%

exp :: { Exp }
  : var '=' exp { Let $1 $3 }
  | var vars '=' exp { Def $1 $2 $4 }
  | exp '+' exp { binop $1 $2 $3 }
  | exp '-' exp { binop $1 $2 $3 }
  | exp '*' exp { binop $1 $2 $3 }
  | exp '/' exp { binop $1 $2 $3 }
  | exp arg { Apply $1 $2 }
  | arg { $1 }

exps :: { [Exp] }
  : exp { [$1] }
  | exps ';' exp { $3 : $1 }

arg :: { Exp }
  : int { Int $1 }
  | var { Var $1 }
  | '(' exps ')' { exps $2 }

vars :: { [Var] }
  : var { [$1 :: Var] }
  | vars var { $2 : $1 }

{

parse :: [Token] -> Exp

parseError :: [Token] -> a
parseError _ = error "Parse error"

exps :: [Exp] -> Exp
exps = foldl1 (flip Seq)

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Apply (Var $ show op) e1) e2

}
