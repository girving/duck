-- Duck parser

-- shift/reduce conflicts: exactly 1
--
-- This conflict is due to nested case expressions:
--   case x of _ -> case y of _ -> a | _ -> b
-- Since we want the alternative to bind to the inner case, resolving
-- the conflict via shift is good.  Removing this would be annoying
-- since we'd need two kinds of case productions, and it will also
-- vanish when we add whitespace dependent syntax.

{
{-# OPTIONS_GHC -w #-}

module Parse (lex, parse) where

import Var
import Lex
import Ast
import Type
import ParseMonad
import ParseOps
import qualified Data.Map as Map

}

%name parse
%tokentype { Token }

%monad { P }
%lexer { lexwrap } { TokEOF }
%error { parseError }

%token
  var  { TokVar $$ _ }
  cvar { TokCVar $$ _ }
  sym  { TokSym $$ _ }
  csym { TokCSym $$ _ }
  int  { TokInt $$ _ }
  data { TokData _ }
  over { TokOver _ }
  let  { TokLet _ }
  in   { TokIn _ }
  case { TokCase _ }
  of   { TokOf _ }
  '='  { TokEq _ }
  '::' { TokDColon _ }
  ','  { TokComma _ }
  '('  { TokLP _ }
  ')'  { TokRP _ }
  '_'  { TokAny _ }
  '\\' { TokLambda _ }
  '->' { TokArrow _ }
  '|'  { TokOr _ }
  import { TokImport _ }
  infix  { TokInfix $$ _ }

%left ';'
%right '=' '->'

%%

--- Toplevel stuff ---

prog :: { Prog }
  : decls { concat $ reverse $1 }

decls :: { [[Decl]] }
  : {--} { [] }
  | decls decl { $2 : $1 }

decl :: { [Decl] }
  : let var patterns '=' exp { [DefD $2 Nothing (reverse $3) $5] }
  | over ty let var patterns '=' exp { [DefD $4 (Just $2) (reverse $5) $7] }
  | let pattern '=' exp { [LetD $2 $4] }
  | data cvar vars maybeConstructors { [Data $2 (reverse $3) (reverse $4)] }
  | import var {% let V file = $2 in parseFile parse file }
  | infix int asyms {% setPrec $2 $1 $3 }

vars :: { [Var] }
  : {--} { [] }
  | vars var { $2 : $1 }

asyms :: { [Var] }
  : asym { [$1] }
  | asyms ',' asym { $3 : $1 }

maybeConstructors :: { [(CVar,[Type])] }
  : {--} { [] }
  | '=' constructors { $2 }

constructors :: { [(CVar,[Type])] }
  : constructor { [$1] }
  | constructors '|'  constructor { $3 : $1 }

constructor :: { (CVar,[Type]) }
  : cvar ty3s { ($1,reverse $2) }

--- Expressions ---

exp :: { Exp }
  : let var patterns '=' exp in exp { Def $2 (reverse $3) $5 $7 }
  | let pattern '=' exp in exp { Let $2 $4 $6 }
  | '\\' patterns '->' exp { Lambda (reverse $2) $4 }
  | case exp of cases { Case $2 (reverse $4) }
  | exptuple { Apply (Var (tuple $1)) (reverse $1) }
  | exp0 { $1 }

exptuple :: { [Exp] }
  : exp0 ',' exp0 { [$3,$1] }
  | exptuple ',' exp0 { $3 : $1 }

exp0 :: { Exp }
  : exp1 { $1 }
  | exp1 '::' ty3 { TypeCheck $1 $3 }

exp1 :: { Exp }
  : ops {% parseOps $1 }
  | exp2 { $1 }

ops :: { ([Exp],[Var]) }
  : ops asym exp2 { let (e,o) = $1 in ($3:e,$2:o) }
  | exp2 asym exp2 { ([$3,$1],[$2]) }

asym :: { Var }
  : sym { $1 }
  | csym { $1 }

exp2 :: { Exp }
  : apply { let f : a = reverse $1 in Apply f a }
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

--- Patterns ---

patterns :: { [Pattern] }
  : pattern2 { [$1] }
  | patterns pattern2 { $2 : $1 }

-- allow empty
patterns_ :: { [Pattern] }
  : {--} { [] }
  | patterns_ pattern2 { $2 : $1 }

pattern :: { Pattern }
  : pattern1 { $1 }
  | pattuple { PatCons (tuple $1) (reverse $1) }

pattern1 :: { Pattern }
  : pattern2 { $1 }
  | cvar patterns_ { PatCons $1 (reverse $2) }
  | pattern2 '::' ty3 { PatType $1 $3 }

pattern2 :: { Pattern }
  : var { PatVar $1 }
  | '_' { PatAny }
  | '(' pattern ')' { $2 }

pattuple :: { [Pattern] }
  : pattern1 ',' pattern1 { [$3,$1] }
  | pattuple ',' pattern1 { $3 : $1 }

--- Tuples ---

ty :: { Type }
  : ty1 { $1 }
  | tytuple { TyApply (tuple $1) (reverse $1) }

ty1 :: { Type }
  : ty2 { $1 }
  | ty2 '->' ty1 { TyFun $1 $3 }

ty2 :: { Type }
  : ty3 { $1 }
  | cvar ty3s { tyapply $1 (reverse $2) }

ty3 :: { Type }
  : var { TyVar $1 }
  | '(' ty ')' { $2 }

tytuple :: { [Type] }
  : ty1 ',' ty1 { [$3,$1] }
  | tytuple ',' ty1 { $3 : $1 }

ty3s :: { [Type] }
  : {--} { [] }
  | ty3s ty3 { $2 : $1 }

{

parse :: P Prog

parseError :: Token -> P a
parseError t = fail ("syntax error at '" ++ show t ++ "'")

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ V $ show op) [e1, e2]

tyapply :: CVar -> [Type] -> Type
tyapply (V "Int") [] = TyInt
tyapply (V "Void") [] = TyVoid
tyapply c args = TyApply c args

setPrec :: Int -> Fixity -> [Var] -> P [Decl]
setPrec p d syms = do
  s <- get
  put $ s { ps_prec = foldl (\f v -> Map.insert v (p,d) f) (ps_prec s) syms }
  return $ [Infix p d (reverse syms)]

}
