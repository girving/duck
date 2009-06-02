-- Duck parser

-- shift/reduce conflicts: exactly 7
--
-- The first conflict is due to nested case expressions:
--   case x of _ -> case y of _ -> a | _ -> b
-- Since we want the alternative to bind to the inner case, resolving
-- the conflict via shift is good.  Removing this would be annoying
-- since we'd need two kinds of case productions, and it will also
-- vanish when we add whitespace dependent syntax.
--
-- The other 6 are due to expressions like 1 + \x -> x, which we
-- parse as 1 + (\x -> x).  Parsing this requires the lambda rule to
-- go in exp2 (arguments to infix expressions).  Expressions of the
-- form \x -> x + 1 then become ambiguous.  In order to avoid duplicating
-- a slew of expression nonterminals, we let the generator resolve the
-- ambiguity correctly in favor of shift.

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
  if   { TokIf _ }
  then { TokThen _ }
  else { TokElse _ }
  '='  { TokEq _ }
  '::' { TokDColon _ }
  ','  { TokComma _ }
  '('  { TokLP _ }
  ')'  { TokRP _ }
  '['  { TokLB _ }
  ']'  { TokRB _ }
  '_'  { TokAny _ }
  '\\' { TokLambda _ }
  '->' { TokArrow _ }
  '|'  { TokOr _ }
  '-'  { TokMinus _ }
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
  : let avar patterns '=' exp { [DefD $2 Nothing (reverse $3) $5] }
  | let pattern2 sym pattern2 '=' exp { [DefD $3 Nothing [$2,$4] $6] }
  | over ty let avar patterns '=' exp { [DefD $4 (Just $2) (reverse $5) $7] }
  | over ty let pattern2 sym pattern2 '=' exp { [DefD $5 (Just $2) [$4,$6] $8] }
  | let pattern '=' exp { [LetD $2 $4] }
  | import var {% let V file = $2 in parseFile parse file }
  | infix int asyms {% setPrec $2 $1 $3 }
  | data cvar vars maybeConstructors { [Data $2 (reverse $3) (reverse $4)] }
  | data '(' ')' maybeConstructors { [Data (V "()") [] (reverse $4)] } -- type ()
  | data '[' var ']' maybeConstructors { [Data (V "[]") [$3] (reverse $5)] } -- type [a]

avar :: { Var }
  : var { $1 }
  | '(' asym ')' { $2 }
  | '(' if ')' { V "if" }

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
  | ty2 csym ty2 { ($2,[$1,$3]) }
  | '(' ')' { (V "()",[]) }
  | '[' ']' { (V "[]",[]) }

--- Expressions ---

exp :: { Exp }
  : let var patterns '=' exp in exp { Def $2 (reverse $3) $5 $7 }
  | let pattern '=' exp in exp { Let $2 $4 $6 }
  | case exp of cases { Case $2 (reverse $4) }
  | if exp then exp else exp { If $2 $4 $6 }
  | exptuple { Apply (Var (tuple $1)) (reverse $1) }
  | exp0 { $1 }

exps :: { [Exp] }
  : exp0 { [$1] }
  | exps ',' exp0 { $3 : $1 }

exptuple :: { [Exp] }
  : exp0 ',' exp0 { [$3,$1] }
  | exptuple ',' exp0 { $3 : $1 }

exp0 :: { Exp }
  : exp1 { $1 }
  | exp1 '::' ty3 { TypeCheck $1 $3 }

exp1 :: { Exp }
  : ops {% parseExpOps $1 }

ops :: { [Either Exp Var] }
  : ops asym unops { $3 ++ (Right $2 : $1) }
  | unops { $1 }

unops :: { [Either Exp Var] }
  : exp2 { [Left $1] }
  | '-' unops { $2 ++ [Right (V "-")] }

asym :: { Var }
  : sym { $1 }
  | csym { $1 }
  | '-' { V "-" }

exp2 :: { Exp }
  : apply { let f : a = reverse $1 in Apply f a }
  | '\\' patterns '->' exp { Lambda (reverse $2) $4 }
  | arg { $1 }

apply :: { [Exp] }
  : apply arg { $2 : $1 }
  | arg arg { [$2,$1] }

arg :: { Exp }
  : int { Int $1 }
  | var { Var $1 }
  | cvar { Var $1 }
  | '(' exp ')' { $2 }
  | '(' asym ')' { Var $2 }
  | '(' ')' { Var (V "()") }
  | '[' ']' { Var (V "[]") }
  | '[' exps ']' { List (reverse $2) }

cases :: { [(Pattern,Exp)] }
  : pattern '->' exp { [($1,$3)] }
  | cases '|' pattern '->' exp { ($3,$5) : $1 }

--- Patterns ---

patterns :: { [Pattern] }
  : pattern3 { [$1] }
  | patterns pattern3 { $2 : $1 }

pattern :: { Pattern }
  : pattern1 { $1 }
  | pattuple { PatCons (tuple $1) (reverse $1) }

pattern1 :: { Pattern }
  : pattern2 { $1 }
  | patternops {% parsePatOps $1 }

patternops :: { [Either Pattern Var] }
  : patternops csym pattern2 { Left $3 : Right $2 : $1 }
  | pattern2 csym pattern2 { [Left $3,Right $2,Left $1] }

pattern2 :: { Pattern }
  : pattern3 { $1 }
  | cvar patterns { PatCons $1 (reverse $2) }
  | pattern3 '::' ty3 { PatType $1 $3 }

pattern3 :: { Pattern }
  : var { PatVar $1 }
  | cvar { PatCons $1 [] }
  | '_' { PatAny }
  | '(' pattern ')' { $2 }
  | '(' ')' { PatCons (V "()") [] }
  | '[' ']' { PatCons (V "[]") [] }

pattuple :: { [Pattern] }
  : pattern1 ',' pattern1 { [$3,$1] }
  | pattuple ',' pattern1 { $3 : $1 }

--- Types ---

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
  | '[' ty ']' { TyApply (V "[]") [$2] }

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
tyapply (V "IO") [t] = TyIO t
tyapply (V "Int") [] = TyInt
tyapply (V "Void") [] = TyVoid
tyapply c args = TyApply c args

setPrec :: Int -> Fixity -> [Var] -> P [Decl]
setPrec p d syms = do
  s <- get
  put $ s { ps_prec = foldl (\f v -> Map.insert v (p,d) f) (ps_prec s) syms }
  return $ [Infix p d (reverse syms)]

}
