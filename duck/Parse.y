-- | Duck parser

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
import Pretty
import Util

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
  : exp0 '::' ty {% spec $1 >.= \v -> [loc $1 $> $SpecD v (unLoc $3)] }
  | exp '=' exp {% lefthandside $1 >.= \l -> [loc $1 $> $ either (\p -> LetD p (expLoc $3)) (\ (v,pl) -> DefD v pl (expLoc $3)) l] }
  | import var {% let V file = var $2 in parseFile parse file }
  | infix int asyms { [loc $1 $> $ Infix (int $2,ifix $1) (reverse (unLoc $3))] }
  | data dvar lvars maybeConstructors { [loc $1 $> $ Data (unLoc $2) (reverse (unLoc $3)) (reverse (unLoc $4))] }

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

-- An underscore after a nonterminal (exp_) means it cannot contain a parenthesis-killing backslash expression.
-- This duplication is unfortunately, but I finally got tired of the shift-reduce conflicts.

exp :: { Loc Exp }
  : exp0 '::' ty { loc $1 $> $ Spec (expLoc $1) (unLoc $3) }
  | exp0 { $1 }

exp0 :: { Loc Exp }
  : let exp '=' exp in exp0 {% lefthandside $2 >.= \l -> loc $1 $> $ either (\p -> Let p (expLoc $4) (expLoc $6)) (\ (v,pl) -> Def v pl (expLoc $4) (expLoc $6)) l }
  | case exp of '{' cases '}' { loc $1 $> $ Case (expLoc $2) (reverse $5) }
  | if exp then exp else exp0 { loc $1 $> $ If (expLoc $2) (expLoc $4) (expLoc $6) }
  | arrow { fmap (\ (p,e) -> Lambda [p] e) $1 }
  | exp1 { $1 }

arrow :: { Loc (Pattern,Exp) }
  : exp1_ '->' exp0 {% pattern $1 >.= \p -> loc $1 $> (patLoc p,expLoc $3) }

cases :: { [(Pattern,Exp)] }
  : arrow { [unLoc $1] }
  | cases ';' arrow { unLoc $3 : $1 }

exp1 :: { Loc Exp }
  : commas { fmap tuple $1 }

exp1_ :: { Loc Exp }
  : commas_ { fmap tuple $1 }

commas :: { Loc [Exp] }
  : exp2 { loc1 $1 [expLoc $1] }
  | commas_ ',' exp2 { loc $1 $> $ expLoc $3 : unLoc $1 }

commas_ :: { Loc [Exp] }
  : exp2_ { loc1 $1 [expLoc $1] }
  | commas_ ',' exp2_ { loc $1 $> $ expLoc $3 : unLoc $1 }

exp2 :: { Loc Exp }
  : ops { fmap ops $1 }

exp2_ :: { Loc Exp }
  : ops_ { fmap ops $1 }

ops :: { Loc (Ops Exp) }
  : ops_ asym unops { loc $1 $> $ OpBin (unLoc $2) (unLoc $1) (unLoc $3) }
  | unops { $1 }

ops_ :: { Loc (Ops Exp) }
  : ops_ asym unops_ { loc $1 $> $ OpBin (unLoc $2) (unLoc $1) (unLoc $3) }
  | unops_ { $1 }

unops :: { Loc (Ops Exp) }
  : exp3 { loc1 $1 $ OpAtom (expLoc $1) }
  | '-' unops { loc $1 $> $ OpUn (V "-") (unLoc $2) }

unops_ :: { Loc (Ops Exp) }
  : exp3_ { loc1 $1 $ OpAtom (expLoc $1) }
  | '-' unops_ { loc $1 $> $ OpUn (V "-") (unLoc $2) }

exp3 :: { Loc Exp }
  : exps { fmap apply $1 }

exp3_ :: { Loc Exp }
  : exps_ { fmap apply $1 }

exps :: { Loc [Exp] }
  : atom { fmap (:[]) $1 }
  | exps_ atom { loc $1 $> $ expLoc $2 : unLoc $1 }

exps_ :: { Loc [Exp] }
  : atom_ { fmap (:[]) $1 }
  | exps_ atom_ { loc $1 $> $ expLoc $2 : unLoc $1 }

atom :: { Loc Exp }
  : atom_ { $1 }
  | '\\' exp0 { loc $1 $> (expLoc $2) }

atom_ :: { Loc Exp }
  : int { fmap (Int . tokInt) $1 }
  | lvar { fmap Var $1 }
  | cvar { fmap Var $ locVar $1 }
  | '_' { loc1 $1 Any }
  | '(' exp ')' { $2 }
  | '(' exp error {% unmatched $1 }
  | '(' ')' { loc $1 $> $ Var (V "()") }
  | '[' ']' { loc $1 $> $ Var (V "[]") }
  | '[' commas ']' { loc $1 $> $ List (reverse (unLoc $2)) }
  | '[' commas error {% unmatched $1 }

--- Variables ---

lvar :: { Loc Var }
  : var { locVar $1 }
  | '(' sym ')' { loc $1 $> (var $2) }
  | '(' '-' ')' { loc $1 $> (V "-") }
  | '(' if ')' { loc $1 $> (V "if") }

lvars :: { Loc [Var] }
  : {--} { loc0 [] }
  | lvars var { loc $1 $> $ var $2 : unLoc $1 }

dvar :: { Loc Var }
  : cvar { locVar $1 }
  | '(' ')' { loc $1 $> $ V "()" } -- type ()

asym :: { Loc Var }
  : sym { locVar $1 }
  | csym { locVar $1 }
  | '-' { loc1 $1 $ V "-" }

asyms :: { Loc [Var] }
  : asym { fmap (:[]) $1 }
  | asyms asym { loc $1 $> $ unLoc $2 : unLoc $1 }

--- Types ---

ty :: { Loc TypeSet }
  : ty1 { $1 }
  | tytuple { fmap (\tt -> TsCons (tupleCons tt) (reverse tt)) $1 }

ty1 :: { Loc TypeSet }
  : ty2 { $1 }
  | ty2 '->' ty1 { loc $1 $> $ TsFun (unLoc $1) (unLoc $3) }

ty2 :: { Loc TypeSet }
  : ty3 { $1 }
  | cvar ty3s { loc $1 $> $ tycons (var $1) (reverse (unLoc $2)) }

ty3 :: { Loc TypeSet }
  : var { fmap (TsVar . tokVar) $1 }
  | cvar { fmap (\t -> tycons (tokVar t) []) $1 }
  | '(' ty ')' { $2 }

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
patLoc (Loc l (PatLoc _ e)) = patLoc (Loc l e) -- shouldn't happen
patLoc (Loc l p)
  | hasLoc l = PatLoc l p
  | otherwise = p

apply :: [Exp] -> Exp
apply [] = undefined
apply [e] = e
apply el | f:args <- reverse el = Apply f args

tuple :: [Exp] -> Exp
tuple [e] = e
tuple el = Apply (Var (tupleCons el)) (reverse el)

ops :: Ops Exp -> Exp
ops (OpAtom e) = e
ops o = Ops o

pattern :: Loc Exp -> P (Loc Pattern)
pattern (Loc l e) = Loc l =.< patternExp l e

patterns :: Loc [Exp] -> P (Loc [Pattern])
patterns (Loc l el) = Loc l =.< mapM (patternExp l) el

patternExp :: SrcLoc -> Exp -> P Pattern
patternExp l (Apply e el) | Just c <- unVar e, isCons c = PatCons c =.< mapM (patternExp l) el
patternExp l (Apply e _) = parseError (ParseError l ("only constructors can be applied in patterns, not '"++show (pretty e)++"'"))
patternExp l (Var c) | isCons c = return $ PatCons c []
patternExp l (Var v) = return $ PatVar v
patternExp l Any = return $ PatAny
patternExp l (List el) = PatList =.< mapM (patternExp l) el
patternExp l (Ops ops) = PatOps =.< patternOps l ops
patternExp l (Spec e t) = patternExp l e >.= \p -> PatSpec p t
patternExp _ (ExpLoc l e) = PatLoc l =.< patternExp l e
patternExp l (Int _) = parseError (ParseError l ("integer patterns aren't implemented yet"))
patternExp l (Def _ _ _ _) = parseError (ParseError l ("let expression not allowed in pattern"))
patternExp l (Let _ _ _) = parseError (ParseError l ("let expression not allowed in pattern"))
patternExp l (Lambda _ _) = parseError (ParseError l ("'->' expression not allowed in pattern"))
patternExp l (Case _ _) = parseError (ParseError l ("case expression not allowed in pattern"))
patternExp l (If _ _ _) = parseError (ParseError l ("if expression not allowed in pattern"))

patternOps :: SrcLoc -> Ops Exp -> P (Ops Pattern)
patternOps l (OpAtom e) = OpAtom =.< patternExp l e
patternOps l (OpBin v o1 o2) | isCons v = do
  p1 <- patternOps l o1
  p2 <- patternOps l o2
  return $ OpBin v p1 p2
patternOps l (OpBin v _ _) = parseError (ParseError l ("only constructor operators are allowed in patterns, not '"++show (pretty v)++"'"))
patternOps l (OpUn v _) = parseError (ParseError l ("unary operator '"++show (pretty v)++"' not allowed in pattern"))

-- Reparse an expression on the left side of an '=' into either a pattern
-- (for a let) or a function declaraction (for a def).
lefthandside :: Loc Exp -> P (Either Pattern (Var, [Pattern]))
lefthandside (Loc _ (ExpLoc l e)) = lefthandside (Loc l e)
lefthandside (Loc l (Apply e el)) | Just v <- unVar e, not (isCons v) = do
  pl <- mapM (patternExp l) el
  return $ Right (v,pl)
lefthandside (Loc l (Ops (OpBin v o1 o2))) | not (isCons v) = do
  p1 <- patternOps l o1
  p2 <- patternOps l o2
  return $ Right (v, map PatOps [p1,p2])
lefthandside (Loc l p) = Left =.< patternExp l p

unVar :: Exp -> Maybe Var
unVar (Var v) = Just v
unVar (ExpLoc _ e) = unVar e
unVar _ = Nothing

-- Currently, specifications are only allowed to be single lowercase variables
spec :: Loc Exp -> P Var
spec (Loc l e) | Just v <- unVar e = return v
spec (Loc l e) = parseError (ParseError l ("only variables are allowed in top level type specifications, not '"++show (pretty e)++"'"))

}
