-- Duck parser

{
{-# OPTIONS_GHC -w #-}

module Parse (lex, parse) where

import Var
import Lex
import Ast

}

%name parse
%tokentype { Token }
%error { parseError }

%token
  var { TokVar $$ }
  int { TokInt $$ }
  -- def { TokDef }
  let { TokLet }
  in  { TokIn }
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
  '_' { TokAny }
  '\\' { TokLambda }
  '->' { TokArrow }

%left ';'
%right '='
%left '+' '-'
%left '*' '/'

%%

prog :: { Prog }
  : decls { reverse $1 }

decls :: { [Decl] }
  : {--} { [] }
  | decls decl { $2 : $1 }

decl :: { Decl }
  : let var patterns '=' exp { DefD $2 (reverse $3) $5 }
  | let pattern '=' exp { LetD $2 $4 }

exps :: { [Exp] }
  : exp { [$1] }
  | exps ';' exp { $3 : $1 }

exp :: { Exp }
  : let var patterns '=' exp in exp { Def $2 (reverse $3) $5 $7 }
  | let pattern '=' exp in exp { Let $2 $4 $6 }
  | '\\' patterns '->' exp { Lambda (reverse $2) $4 }
  | exp1 { $1 }

exp1 :: { Exp }
  : exp1 '+' exp1 { binop $1 $2 $3 }
  | exp1 '-' exp1 { binop $1 $2 $3 }
  | exp1 '*' exp1 { binop $1 $2 $3 }
  | exp1 '/' exp1 { binop $1 $2 $3 }
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
  | '_' { PatAny }
  | '(' patterns ')' { wrap PatTuple $2 }
  | pattern ':' ty { PatType $1 $3 }

tytuple :: { [Type] }
  : ty { [$1] }
  | tytuple ',' ty { $3 : $1 }

ty :: { Type }
  : var { TyVar $1 }
  | '(' tytuple ')' { wrap TyTuple $2 }

{

parse :: [Token] -> Prog

parseError :: [Token] -> a
parseError _ = error "Parse error"

exps :: [Exp] -> Exp
exps = Seq . reverse

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ V $ show op) [e1, e2]

wrap :: ([a] -> a) -> [a] -> a
wrap f [x] = x
wrap f xl = f $ reverse xl

{-
-- Turn an expression into pattern.  This is used to
-- turn exp = exp into pat = exp, since doing this within
-- the grammar would violate LALR(1)
topattern :: Exp -> Pattern
topattern p = case p of
  Var v -> PatVar v
  _ -> error "Invalid pattern"
-}

}
