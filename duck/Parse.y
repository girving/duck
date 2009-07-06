-- | Duck parser

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
import SrcLoc
import ParseMonad
import ParseOps
import qualified Data.Map as Map

}

%name parse
%tokentype { Loc Token }

%monad { P }
%lexer { lexwrap } { Loc _ TokEOF }
%error { parserError }

%token
  var  { Loc _ (TokVar _) }
  cvar { Loc _ (TokCVar _) }
  sym  { Loc _ (TokSym _) }
  csym { Loc _ (TokCSym _) }
  int  { Loc _ (TokInt _) }
  data { Loc _ (TokData) }
  over { Loc _ (TokOver) }
  let  { Loc _ (TokLet) }
  in   { Loc _ (TokIn) }
  case { Loc _ (TokCase) }
  of   { Loc _ (TokOf) }
  if   { Loc _ (TokIf) }
  then { Loc _ (TokThen) }
  else { Loc _ (TokElse) }
  '='  { Loc _ (TokEq) }
  '::' { Loc _ (TokDColon) }
  ','  { Loc _ (TokComma) }
  '('  { Loc _ (TokLP) }
  ')'  { Loc _ (TokRP) }
  '['  { Loc _ (TokLB) }
  ']'  { Loc _ (TokRB) }
  '_'  { Loc _ (TokAny) }
  '\\' { Loc _ (TokLambda) }
  '->' { Loc _ (TokArrow) }
  '|'  { Loc _ (TokOr) }
  '-'  { Loc _ (TokMinus) }
  import { Loc _ (TokImport) }
  infix  { Loc _ (TokInfix $$) }

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
  : let avar patterns '=' exp { [DefD $2 Nothing (reverse (unLoc $3)) (expLoc $5)] }
  | let pattern2 sym pattern2 '=' exp { [DefD (var $3) Nothing [patLoc $2,patLoc $4] (expLoc $6)] }
  | over ty let avar patterns '=' exp { [DefD $4 (Just $2) (reverse (unLoc $5)) (expLoc $7)] }
  | over ty let pattern2 sym pattern2 '=' exp { [DefD (var $5) (Just $2) [patLoc $4,patLoc $6] (expLoc $8)] }
  | let pattern '=' exp { [LetD (patLoc $2) (expLoc $4)] }
  | import var {% let V file = var $2 in parseFile parse file }
  | infix int asyms { [Infix (int $2,$1) (reverse $3)] }
  | data cvar vars maybeConstructors { [Data (var $2) (reverse $3) (reverse $4)] }
  | data '(' ')' maybeConstructors { [Data (V "()") [] (reverse $4)] } -- type ()
  | data '[' var ']' maybeConstructors { [Data (V "[]") [var $3] (reverse $5)] } -- type [a]

avar :: { Var }
  : var { var $1 }
  | '(' asym ')' { unLoc $2 }
  | '(' if ')' { V "if" }

vars :: { [Var] }
  : {--} { [] }
  | vars var { var $2 : $1 }

asyms :: { [Var] }
  : asym { [unLoc $1] }
  | asyms ',' asym { unLoc $3 : $1 }

maybeConstructors :: { [(CVar,[Type])] }
  : {--} { [] }
  | '=' constructors { $2 }

constructors :: { [(CVar,[Type])] }
  : constructor { [$1] }
  | constructors '|'  constructor { $3 : $1 }

constructor :: { (CVar,[Type]) }
  : cvar ty3s { (var $1,reverse $2) }
  | ty2 csym ty2 { (var $2,[$1,$3]) }
  | '(' ')' { (V "()",[]) }
  | '[' ']' { (V "[]",[]) }

--- Expressions ---

exp :: { Loc Exp }
  : let var patterns '=' exp in exp { loc $1 $> $ Def (var $2) (reverse (unLoc $3)) (expLoc $5) (expLoc $7) }
  | let pattern '=' exp in exp { loc $1 $> $ Let (patLoc $2) (expLoc $4) (expLoc $6) }
  | case exp of cases { loc $1 $> $ Case (expLoc $2) (reverse (unLoc $4)) }
  | if exp then exp else exp { loc $1 $> $ If (expLoc $2) (expLoc $4) (expLoc $6) }
  | exptuple { fmap (\et -> Apply (Var (tuple et)) (reverse et)) $1 }
  | exp0 { $1 }

exps :: { [Exp] }
  : exp0 { [expLoc $1] }
  | exps ',' exp0 { expLoc $3 : $1 }

exptuple :: { Loc [Exp] }
  : exp0 ',' exp0 { loc $1 $> $ [expLoc $3,expLoc $1] }
  | exptuple ',' exp0 { loc $1 $> $ expLoc $3 : unLoc $1 }

exp0 :: { Loc Exp }
  : exp1 { $1 }
  | exp1 '::' ty3 { loc1 $1 $ TypeCheck (unLoc $1) $3 }

exp1 :: { Loc Exp }
  : ops { fmap Ops $1 }

ops :: { Loc (Ops Exp) }
  : ops asym unops { loc $1 $> $ OpBin (unLoc $2) (unLoc $1) (unLoc $3) }
  | unops { $1 }

unops :: { Loc (Ops Exp) }
  : exp2 { loc1 $1 $ OpAtom (expLoc $1) }
  | '-' unops { loc $1 $> $ OpUn (V "-") (unLoc $2) }

asym :: { Loc Var }
  : sym { locVar $1 }
  | csym { locVar $1 }
  | '-' { loc1 $1 $ V "-" }

exp2 :: { Loc Exp }
  : apply { fmap (\fa -> let f:a = reverse fa in Apply f a) $1 }
  | '\\' patterns '->' exp { loc $1 $> $ Lambda (reverse (unLoc $2)) (expLoc $4) }
  | arg { $1 }

apply :: { Loc [Exp] }
  : apply arg { loc $1 $> $ expLoc $2 : unLoc $1 }
  | arg arg { loc $1 $> $ [expLoc $2,expLoc $1] }

arg :: { Loc Exp }
  : int { fmap (Int . tokInt) $1 }
  | var { fmap Var $ locVar $1 }
  | cvar { fmap Var $ locVar $1 }
  | '(' exp ')' { $2 }
  | '(' asym ')' { fmap Var $2 }
  | '(' ')' { loc $1 $> $ Var (V "()") }
  | '[' ']' { loc $1 $> $ Var (V "[]") }
  | '[' exps ']' { loc $1 $> $ List (reverse $2) }

cases :: { Loc [(Pattern,Exp)] }
  : pattern '->' exp { loc $1 $> $ [(patLoc $1,expLoc $3)] }
  | cases '|' pattern '->' exp { loc $1 $> $ (patLoc $3,expLoc $5) : unLoc $1 }

--- Patterns ---

patterns :: { Loc [Pattern] }
  : pattern3 { loc1 $1 $ [patLoc $1] }
  | patterns pattern3 { loc $1 $> $ patLoc $2 : unLoc $1 }

pattern :: { Loc Pattern }
  : pattern1 { $1 }
  | pattuple { fmap (\pt -> PatCons (tuple pt) (reverse pt)) $1 }

pattern1 :: { Loc Pattern }
  : pattern2 { $1 }
  | patternops { fmap PatOps $1 }

patternops :: { Loc (Ops Pattern) }
  : patternops csym pattern2 { loc $1 $> $ OpBin (var $2) (unLoc $1) (OpAtom (patLoc $3)) }
  | pattern2 csym pattern2 { loc $1 $> $ OpBin (var $2) (OpAtom (patLoc $1)) (OpAtom (patLoc $3)) }

pattern2 :: { Loc Pattern }
  : pattern3 { $1 }
  | cvar patterns { loc $1 $> $ PatCons (var $1) (reverse (unLoc $2)) }
  | pattern3 '::' ty3 { loc1 $1 $ PatType (unLoc $1) $3 }

pattern3 :: { Loc Pattern }
  : var { fmap PatVar $ locVar $1 }
  | cvar { fmap (\v -> PatCons v []) (locVar $1) }
  | '_' { loc1 $1 PatAny }
  | '(' pattern ')' { $2 }
  | '(' ')' { loc $1 $> $ PatCons (V "()") [] }
  | '[' ']' { loc $1 $> $ PatCons (V "[]") [] }

pattuple :: { Loc [Pattern] }
  : pattern1 ',' pattern1 { loc $1 $> $ [patLoc $3,patLoc $1] }
  | pattuple ',' pattern1 { loc $1 $> $ patLoc $3 : unLoc $1 }

--- Types ---

ty :: { Type }
  : ty1 { $1 }
  | tytuple { TyApply (tuple $1) (reverse $1) }

ty1 :: { Type }
  : ty2 { $1 }
  | ty2 '->' ty1 { TyFun $1 $3 }

ty2 :: { Type }
  : ty3 { $1 }
  | cvar ty3s { tyapply (var $1) (reverse $2) }

ty3 :: { Type }
  : var { TyVar (var $1) }
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

parserError :: Loc Token -> P a
parserError (Loc l t) = parseError (ParseError l ("syntax error at '" ++ show t ++ "'"))

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ V $ show op) [e1, e2]

tyapply :: CVar -> [Type] -> Type
tyapply (V "IO") [t] = TyIO t
tyapply (V "Int") [] = TyInt
tyapply (V "Void") [] = TyVoid
tyapply c args = TyApply c args

var :: Loc Token -> Var
var = tokVar . unLoc

int :: Loc Token -> Int
int = tokInt . unLoc

loc :: Loc x -> Loc y -> a -> Loc a
loc (Loc l _) (Loc r _) = Loc (srcRng l r)

loc1 :: Loc x -> a -> Loc a
loc1 (Loc l _) = Loc l

locVar :: Loc Token -> Loc Var
locVar = fmap tokVar

expLoc :: Loc Exp -> Exp
expLoc (Loc l (ExpLoc _ e)) = expLoc (Loc l e) -- shouldn't happen
expLoc (Loc l e)
  | hasLoc l = ExpLoc l e
  | otherwise = e

patLoc :: Loc Pattern -> Pattern
patLoc = unLoc -- no PatLoc (yet)

}
