-- | Duck parser

-- shift/reduce conflicts: exactly 5
--
-- These are due to expressions like 1 + \x -> x, which we
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
import Token
import Layout
import Ast
import Type
import SrcLoc
import ParseMonad
import ParseOps
import qualified Data.Map as Map
import Data.Monoid (mappend, mconcat)

}

%name parse
%tokentype { Loc Token }

%monad { P }
%lexer { (layout lexer >>=) } { Loc _ TokEOF } -- Happy wants the lexer in continuation form
%error { parserError }

%token
  var  { Loc _ (TokVar _) }
  cvar { Loc _ (TokCVar _) }
  sym  { Loc _ (TokSym _) }
  csym { Loc _ (TokCSym _) }
  int  { Loc _ (TokInt _) }
  data { Loc _ (TokData) }
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
  '{'  { Loc _ (TokLC _) }
  '}'  { Loc _ (TokRC _) }
  ';'  { Loc _ (TokSemi _) }
  '_'  { Loc _ (TokAny) }
  '\\' { Loc _ (TokLambda) }
  '->' { Loc _ (TokArrow) }
  -- '|'  { Loc _ (TokOr) }
  '-'  { Loc _ (TokMinus) }
  import { Loc _ (TokImport) }
  infix  { Loc _ (TokInfix _) }

%left ';'
%right '=' '->'

%%

--- Toplevel stuff ---

prog :: { Prog }
  : '{' decls '}' { concat $ reverse $2 }

decls :: { [[Loc Decl]] }
  : {--} { [] }
  | decl { [$1] }
  | decls ';' { $1 }
  | decls ';' decl { $3 : $1 }

decl :: { [Loc Decl] }
  : avar '::' ty { [loc $1 $> $SpecD (unLoc $1) (unLoc $3)] }
  | avar patterns '=' exp { [loc $1 $> $ DefD (unLoc $1) (reverse (unLoc $2)) (expLoc $4)] }
  | pattern2 sym pattern2 '=' exp { [loc $1 $> $ DefD (var $2) [patLoc $1,patLoc $3] (expLoc $5)] }
  | pattern0 '=' exp { [loc $1 $> $ LetD (patLoc $1) (expLoc $3)] }
  | import var {% let V file = var $2 in parseFile parse file }
  | infix int asyms { [loc $1 $> $ Infix (int $2,ifix $1) (reverse (unLoc $3))] }
  | data cvar tyvars maybeConstructors { [Loc (mconcat [srcLoc $1, srcLoc $2, srcLoc $3, srcLoc $4]) $ Data (var $2) (reverse (unLoc $3)) (reverse (unLoc $4))] }
  | data '(' ')' maybeConstructors { [Loc (mconcat [srcLoc $1, srcLoc $3, srcLoc $4]) $ Data (V "()") [] (reverse (unLoc $4))] } -- type ()
  | data '[' var ']' maybeConstructors { [Loc (mconcat [srcLoc $1, srcLoc $4, srcLoc $5]) $ Data (V "[]") [var $3] (reverse (unLoc $5))] } -- type [a]

avar :: { Loc Var }
  : var { locVar $1 }
  | '(' asym ')' { loc $1 $> (unLoc $2) }
  | '(' if ')' { loc $1 $> (V "if") }

tyvars :: { Loc [Var] }
  : {--} { loc0 [] }
  | tyvars var { loc $1 $> $ var $2 : unLoc $1 }

asyms :: { Loc [Var] }
  : asym { fmap (:[]) $1 }
  | asyms ',' asym { loc $1 $> $ unLoc $3 : unLoc $1 }

maybeConstructors :: { Loc [(CVar,[TypeSet])] }
  : {--} { loc0 [] }
  | of '{' constructors '}' { loc $1 $> $ $3 }

constructors :: { [(CVar,[TypeSet])] }
  : constructor { [$1] }
  | constructors ';'  constructor { $3 : $1 }

constructor :: { (CVar,[TypeSet]) }
  : cvar { (var $1,[]) }
  | cvar ty3s { (var $1,reverse (unLoc $2)) }
  | ty2 csym ty2 { (var $2,[unLoc $1,unLoc $3]) }
  | '(' ')' { (V "()",[]) }
  | '[' ']' { (V "[]",[]) }

--- Expressions ---

exp :: { Loc Exp }
  : exp0 { $1 }
  | exp0 '::' ty { loc $1 $> $ TypeCheck (expLoc $1) (unLoc $3) }

exp0 :: { Loc Exp }
  : let avar patterns '=' exp in exp0 { loc $1 $> $ Def (unLoc $2) (reverse (unLoc $3)) (expLoc $5) (expLoc $7) }
  | let pattern '=' exp in exp0 { loc $1 $> $ Let (patLoc $2) (expLoc $4) (expLoc $6) }
  | case exp of '{' cases '}' { loc $1 $> $ Case (expLoc $2) (reverse $5) }
  | if exp then exp else exp0 { loc $1 $> $ If (expLoc $2) (expLoc $4) (expLoc $6) }
  | exptuple { fmap (\et -> Apply (Var (tuple et)) (reverse et)) $1 }
  | exp1 { $1 }

cases :: { [(Pattern,Exp)] }
  : onecase { [$1] }
  | cases ';' onecase { $3 : $1 }

onecase :: { (Pattern,Exp) }
  : pattern0 '->' exp { (patLoc $1,expLoc $3) }

exps :: { [Exp] }
  : exp1 { [expLoc $1] }
  | exps ',' exp1 { expLoc $3 : $1 }

exptuple :: { Loc [Exp] }
  : exp1 ',' exp1 { loc $1 $> $ [expLoc $3,expLoc $1] }
  | exptuple ',' exp1 { loc $1 $> $ expLoc $3 : unLoc $1 }

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
  : apply { fmap ((\(f:a) -> Apply f a) . reverse) $1 }
  | '\\' patterns '->' exp0 { loc $1 $> $ Lambda (reverse (unLoc $2)) (expLoc $4) }
  | arg { $1 }

apply :: { Loc [Exp] }
  : apply arg { loc $1 $> $ expLoc $2 : unLoc $1 }
  | arg arg { loc $1 $> $ [expLoc $2,expLoc $1] }

arg :: { Loc Exp }
  : int { fmap (Int . tokInt) $1 }
  | avar { fmap Var $1 }
  | cvar { fmap Var $ locVar $1 }
  | '(' exp ')' { $2 }
  | '(' exp error {% unmatched $1 }
  | '(' ')' { loc $1 $> $ Var (V "()") }
  | '[' ']' { loc $1 $> $ Var (V "[]") }
  | '[' exps ']' { loc $1 $> $ List (reverse $2) }
  | '[' exps error {% unmatched $1 }

--- Patterns ---

pattern :: { Loc Pattern }
  : pattern0 { $1 }
  | pattern0 '::' ty { loc $1 $> $ PatType (patLoc $1) (unLoc $3) }

pattern0 :: { Loc Pattern }
  : pattern1 { $1 }
  | pattuple { fmap (\pt -> PatCons (tuple pt) (reverse pt)) $1 }

pattuple :: { Loc [Pattern] }
  : pattern1 ',' pattern1 { loc $1 $> $ [patLoc $3,patLoc $1] }
  | pattuple ',' pattern1 { loc $1 $> $ patLoc $3 : unLoc $1 }

pattern1 :: { Loc Pattern }
  : pattern2 { $1 }
  | patternops { fmap PatOps $1 }

patternops :: { Loc (Ops Pattern) }
  : patternops csym pattern2 { loc $1 $> $ OpBin (var $2) (unLoc $1) (OpAtom (patLoc $3)) }
  | pattern2 csym pattern2 { loc $1 $> $ OpBin (var $2) (OpAtom (patLoc $1)) (OpAtom (patLoc $3)) }

pattern2 :: { Loc Pattern }
  : pattern3 { $1 }
  | cvar patterns { loc $1 $> $ PatCons (var $1) (reverse (unLoc $2)) }

patterns :: { Loc [Pattern] }
  : pattern3 { loc1 $1 $ [patLoc $1] }
  | patterns pattern3 { loc $1 $> $ patLoc $2 : unLoc $1 }

pattern3 :: { Loc Pattern }
  : avar { fmap PatVar $1 }
  | cvar { fmap (\v -> PatCons v []) (locVar $1) }
  | '_' { loc1 $1 PatAny }
  | '(' pattern ')' { $2 }
  | '(' ')' { loc $1 $> $ PatCons (V "()") [] }
  | '[' ']' { loc $1 $> $ PatCons (V "[]") [] }

--- Types ---

ty :: { Loc TypeSet }
  : ty1 { $1 }
  | tytuple { fmap (\tt -> TsCons (tuple tt) (reverse tt)) $1 }

ty1 :: { Loc TypeSet }
  : ty2 { $1 }
  | ty2 '->' ty1 { loc $1 $> $ TsFun (unLoc $1) (unLoc $3) }

ty2 :: { Loc TypeSet }
  : ty3 { $1 }
  | cvar ty3s { loc $1 $> $ tycons (var $1) (reverse (unLoc $2)) }

ty3 :: { Loc TypeSet }
  : var { fmap (TsVar . tokVar) $1 }
  | cvar { fmap (\t -> tycons (tokVar t) []) $1 }
  | '(' ty ')' { loc $1 $> $ unLoc $2 }
  | '[' ty ']' { loc $1 $> $ TsCons (V "[]") [unLoc $2] }

tytuple :: { Loc [TypeSet] }
  : ty1 ',' ty1 { loc $1 $> $ [unLoc $3,unLoc $1] }
  | tytuple ',' ty1 { loc $1 $> $ unLoc $3 : unLoc $1 }

ty3s :: { Loc [TypeSet] }
  : ty3 { fmap (\t -> [t]) $1 }
  | ty3s ty3 { loc $1 $> $ unLoc $2 : unLoc $1 }

{

parse :: P Prog

parserError :: Loc Token -> P a
parserError (Loc l t) = parseError (ParseError l ("syntax error "++showAt t))

unmatched :: Loc Token -> P a
unmatched (Loc l t) = parseError (ParseError l ("unmatched '"++show t++"' from "++show l))

binop :: Exp -> Token -> Exp -> Exp
binop e1 op e2 = Apply (Var $ V $ show op) [e1, e2]

tycons :: CVar -> [TypeSet] -> TypeSet
tycons (V "IO") [t] = TsIO t
tycons (V "Int") [] = TsInt
tycons (V "Void") [] = TsVoid
tycons c args = TsCons c args

var :: Loc Token -> Var
var = tokVar . unLoc

int :: Loc Token -> Int
int = tokInt . unLoc

ifix :: Loc Token -> Fixity
ifix = tokFix . unLoc

loc :: Loc x -> Loc y -> a -> Loc a
loc (Loc l _) (Loc r _) = Loc (mappend l r)

loc1 :: Loc x -> a -> Loc a
loc1 (Loc l _) = Loc l

loc0 :: a -> Loc a
loc0 = Loc noLoc

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
