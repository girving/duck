-- Duck parser

{
{-# OPTIONS_GHC -w #-}

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
  def { TokDef }
  ';' { TokSep }
  '=' { TokEq }
  '+' { TokPlus }
  '-' { TokMinus }
  '*' { TokTimes }
  '/' { TokDiv }
  ':' { TokColon }
  ',' { TokComma }
  '(' { TokLP }
  ')' { TokRP }

%left ';'
%right '='
%left '+' '-'
%left '*' '/'

%%

top :: { Exp }
  : exps { exps $1 }

exps :: { [Exp] }
  : exp { [$1] }
  | exps ';' exp { $3 : $1 }

exp :: { Exp }
  : exp '=' exp { Set (topattern $1) $3 }
  | def var patterns '=' exp { Def $2 (reverse $3) $5 }
  | exp '+' exp { binop $1 $2 $3 }
  | exp '-' exp { binop $1 $2 $3 }
  | exp '*' exp { binop $1 $2 $3 }
  | exp '/' exp { binop $1 $2 $3 }
  | apply { let f : a = reverse $1 in Apply f a }
  | arg { $1 }

apply :: { [Exp] }
  : apply arg { $2 : $1 }
  | arg arg { [$2,$1] }

arg :: { Exp }
  : int { Int $1 }
  | var { Var $1 }
  | '(' exps ')' { exps $2 }

patterns :: { [Pattern] }
  : pattern { [$1] }
  | patterns pattern { $2 : $1 }

pattern :: { Pattern }
  : var { PatVar $1 }
  | '(' patterns ')' { wrap PatTuple $2 }
  | pattern ':' ty { PatType $1 $3 }

tytuple :: { [Type] }
  : ty { [$1] }
  | tytuple ',' ty { $3 : $1 }

ty :: { Type }
  : var { TyVar $1 }
  | '(' tytuple ')' { wrap TyTuple $2 }

{

parse :: [Token] -> Exp

parseError :: [Token] -> a
parseError _ = error "Parse error"

exps :: [Exp] -> Exp
exps = Seq . reverse

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ show op) [e1, e2]

wrap :: ([a] -> a) -> [a] -> a
wrap f [x] = x
wrap f xl = f $ reverse xl

-- Turn an expression into pattern.  This is used to
-- turn exp = exp into pat = exp, since doing this within
-- the grammar would violate LALR(1)
topattern :: Exp -> Pattern
topattern p = case p of
  Var v -> PatVar v
  _ -> error "Invalid pattern"

}
