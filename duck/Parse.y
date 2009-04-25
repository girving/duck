-- Duck parser

{
{-# OPTIONS_GHC -w #-}

module Parse (lex, parse) where

import Var
import Lex
import Ast
import ParseMonad

}

%name parse
%tokentype { Token }

%monad { P }
%lexer { lexwrap } { TokEOF }
%error { parseError }

%token
  var  { TokVar $$ _ }
  cvar { TokCVar $$ _ }
  int  { TokInt $$ _ }
  data { TokData _ }
  over { TokOver _ }
  let  { TokLet _ }
  in   { TokIn _ }
  case { TokCase _ }
  of   { TokOf _ }
  ';'  { TokSep _ }
  '='  { TokEq _ }
  '+'  { TokPlus _ }
  '-'  { TokMinus _ }
  '*'  { TokTimes _ }
  '/'  { TokDiv _ }
  ':'  { TokColon _ }
  ','  { TokComma _ }
  '('  { TokLP _ }
  ')'  { TokRP _ }
  '_'  { TokAny _ }
  '\\' { TokLambda _ }
  '->' { TokArrow _ }
  '|'  { TokOr _ }

%left ';'
%right '=' '->'
%left '+' '-'
%left '*' '/'

%%

prog :: { Prog }
  : decls { reverse $1 }

decls :: { [Decl] }
  : {--} { [] }
  | decls decl { $2 : $1 }

decl :: { Decl }
  : let var patterns '=' exp { DefD $2 Nothing (reverse $3) $5 }
  | over ty let var patterns '=' exp { DefD $4 (Just $2) (reverse $5) $7 }
  | let pattern '=' exp { LetD $2 $4 }
  | data cvar vars maybeConstructors { Data $2 (reverse $3) (reverse $4) }

vars :: { [Var] }
  : {--} { [] }
  | vars var { $2 : $1 }

maybeConstructors :: { [(CVar,[Type])] }
  : {--} { [] }
  | '=' constructors { $2 }

constructors :: { [(CVar,[Type])] }
  : constructor { [$1] }
  | constructors '|'  constructor { $3 : $1 }

constructor :: { (CVar,[Type]) }
  : cvar ty2s { ($1,reverse $2) }

exp :: { Exp }
  : let var patterns '=' exp in exp { Def $2 (reverse $3) $5 $7 }
  | let pattern '=' exp in exp { Let $2 $4 $6 }
  | '\\' patterns '->' exp { Lambda (reverse $2) $4 }
  | case exp of cases { Case $2 (reverse $4) }
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
  | cvar { Var $1 }
  | '(' exp ')' { $2 }

cases :: { [(Pattern,Exp)] }
  : pattern '->' exp { [($1,$3)] }
  | cases '|' pattern '->' exp { ($3,$5) : $1 }

patterns :: { [Pattern] }
  : pattern1 { [$1] }
  | patterns pattern1 { $2 : $1 }

-- allow empty
patterns_ :: { [Pattern] }
  : {--} { [] }
  | patterns_ pattern1 { $2 : $1 }

pattern :: { Pattern }
  : pattern1 { $1 }
  | cvar patterns_ { PatCons $1 (reverse $2) }
  | pattern1 ':' ty2 { PatType $1 $3 }

pattern1 :: { Pattern }
  : var { PatVar $1 }
  | '_' { PatAny }
  | '(' pattuple ')' { wrap (\x -> PatCons (tuple x) x) $2 }

pattuple :: { [Pattern] }
  : pattern { [$1] }
  | pattuple ',' pattern { $3 : $1 }

ty :: { Type }
  : ty1 { $1 }
  | ty1 '->' ty { TyFun $1 $3 }

ty1 :: { Type }
  : ty2 { $1 }
  | cvar ty2s { TyApply $1 (reverse $2) }

ty2 :: { Type }
  : var { TyVar $1 }
  | '(' tytuple ')' { wrap TyTuple $2 }

tytuple :: { [Type] }
  : ty { [$1] }
  | tytuple ',' ty { $3 : $1 }

{-
tys :: { [Type] }
  : {--} { [] }
  | tys ty1 { $2 :: $1 }
-}

ty2s :: { [Type] }
  : {--} { [] }
  | ty2s ty2 { $2 : $1 }

{

parse :: P Prog

parseError :: Token -> P a
parseError t = fail ("syntax error at '" ++ show t ++ "'")

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ V $ show op) [e1, e2]

wrap :: ([a] -> a) -> [a] -> a
wrap f [x] = x
wrap f xl = f $ reverse xl

tuple :: [a] -> Var
tuple x = V (replicate (length x - 1) ',')

}
