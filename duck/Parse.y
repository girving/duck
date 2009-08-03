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
  : exp0 '::' exp0 {% spec $1 >>= \v -> ty $3 >.= \t -> [loc $1 $> $SpecD v (unLoc t)] }
  | exp '=' exp {% lefthandside $1 >.= \l -> [loc $1 $> $ either (\p -> LetD p (expLoc $3)) (\ (v,pl) -> DefD v pl (expLoc $3)) l] }
  | import var {% let V file = var $2 in parseFile parse file }
  | infix int asyms { [loc $1 $> $ Infix (int $2,ifix $1) (reverse (unLoc $3))] }
  | data dvar lvars maybeConstructors { [loc $1 $> $ Data $2 (reverse (unLoc $3)) (reverse (unLoc $4))] }

maybeConstructors :: { Loc [(Loc CVar,[TypeSet])] }
  : {--} { loc0 [] }
  | of '{' constructors '}' { loc $1 $> $ $3 }

constructors :: { [(Loc CVar,[TypeSet])] }
  : constructor { [$1] }
  | constructors ';'  constructor { $3 : $1 }

constructor :: { (Loc CVar,[TypeSet]) }
  : exp2 {% constructor $1 }

--- Expressions ---

-- An underscore after a nonterminal (exp_) means it cannot contain a parenthesis-killing backslash expression.
-- This duplication is unfortunately, but I finally got tired of the shift-reduce conflicts.

exp :: { Loc Exp }
  : exp0 '::' exp0 {% ty $3 >.= \t -> loc $1 $> $ Spec (expLoc $1) (unLoc t) }
  | exp0 { $1 }

exp0 :: { Loc Exp }
  : arrows {% arrows $1 }

arrows :: { Loc (Stack Exp Exp) }
  : notarrow { loc1 $1 (Base (expLoc $1)) }
  | exp1_ '->' arrows { loc $1 $> (expLoc $1 :. unLoc $3) }

notarrow :: { Loc Exp }
  : let exp '=' exp in exp0 {% lefthandside $2 >.= \l -> loc $1 $> $ either (\p -> Let p (expLoc $4) (expLoc $6)) (\ (v,pl) -> Def (unLoc v) pl (expLoc $4) (expLoc $6)) l }
  | case exp of '{' cases '}' { loc $1 $> $ Case (expLoc $2) (reverse $5) }
  | if exp then exp else exp0 { loc $1 $> $ If (expLoc $2) (expLoc $4) (expLoc $6) }
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

{

parse :: P Prog

parserError :: Loc Token -> P a
parserError (Loc l t) = parseError (ParseError l ("syntax error "++showAt t))

unmatched :: Loc Token -> P a
unmatched (Loc l t) = parseError (ParseError l ("unmatched '"++show t++"' from "++show l))

tscons :: CVar -> [TypeSet] -> TypeSet
tscons (V "IO") [t] = TsIO t
tscons (V "Int") [] = TsInt
tscons (V "Void") [] = TsVoid
tscons c args = TsCons c args

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

arrows :: Loc (Stack Exp Exp) -> P (Loc Exp)
arrows (Loc l stack) = case splitStack stack of
  ([],e) -> return $ Loc l e
  (el,e) -> patterns (Loc l el) >.= fmap (\pl -> Lambda pl e)

patternExp :: SrcLoc -> Exp -> P Pattern
patternExp l (Apply e el) | Just (Loc _ c) <- unVar l e, isCons c = PatCons c =.< mapM (patternExp l) el
patternExp l (Apply e _) = parseError (ParseError l ("only constructors can be applied in patterns, not '"++show (pretty e)++"'"))
patternExp l (Var c) | isCons c = return $ PatCons c []
patternExp l (Var v) = return $ PatVar v
patternExp l Any = return PatAny
patternExp l (List el) = PatList =.< mapM (patternExp l) el
patternExp l (Ops ops) = PatOps =.< patternOps l ops
patternExp l (Spec e t) = patternExp l e >.= \p -> PatSpec p t
patternExp l (Lambda pl e) = PatLambda pl =.< patternExp l e
patternExp _ (ExpLoc l e) = PatLoc l =.< patternExp l e
patternExp l (Int _) = parseError (ParseError l ("integer patterns aren't implemented yet"))
patternExp l (Def _ _ _ _) = parseError (ParseError l ("let expression not allowed in pattern"))
patternExp l (Let _ _ _) = parseError (ParseError l ("let expression not allowed in pattern"))
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

ty :: Loc Exp -> P (Loc TypeSet)
ty (Loc l e) = Loc l =.< typeExp l e

tys :: Loc [Exp] -> P (Loc [TypeSet])
tys (Loc l el) = Loc l =.< mapM (typeExp l) el

typeExp :: SrcLoc -> Exp -> P TypeSet
typeExp l (Apply e el) | Just (Loc _ c) <- unVar l e, isCons c = tscons c =.< mapM (typeExp l) el
typeExp l (Apply e _) = parseError (ParseError l ("only constructors can be applied in types, not '"++show (pretty e)++"'"))
typeExp l (Var c) | isCons c = return $ tscons c []
typeExp l (Var v) = return $ TsVar v
typeExp l (Lambda pl e) = do
  tl <- mapM (typePat l) pl
  t <- typeExp l e 
  return $ foldr TsFun t tl
typeExp _ (ExpLoc l e) = typeExp l e
typeExp l (Int _) = parseError (ParseError l ("integer types aren't implemented yet"))
typeExp l Any = parseError (ParseError l ("'_' isn't implemented for types yet"))
typeExp l (Def _ _ _ _) = parseError (ParseError l ("let expression not allowed in type"))
typeExp l (Let _ _ _) = parseError (ParseError l ("let expression not allowed in type"))
typeExp l (Case _ _) = parseError (ParseError l ("case expression not allowed in type"))
typeExp l (If _ _ _) = parseError (ParseError l ("if expression not allowed in type"))
typeExp l (Ops _) = parseError (ParseError l ("operator expression not allowed in type"))
typeExp l (Spec _ _) = parseError (ParseError l ("type specifier expression not allowed in type"))
typeExp l (List _) = parseError (ParseError l ("list expression not allowed in type"))

typePat :: SrcLoc -> Pattern -> P TypeSet
typePat l (PatCons c pl) = tscons c =.< mapM (typePat l) pl
typePat l (PatVar v) = return $ TsVar v
typePat l (PatLambda pl p) = do
  tl <- mapM (typePat l) pl
  t <- typePat l p 
  return $ foldr TsFun t tl
typePat _ (PatLoc l p) = typePat l p
typePat l PatAny = parseError (ParseError l ("'_' isn't implemented for types yet"))
typePat l (PatOps _) = parseError (ParseError l ("operator expression not allowed in type"))
typePat l (PatSpec _ _) = parseError (ParseError l ("type specifier expression not allowed in type"))
typePat l (PatList _) = parseError (ParseError l ("list expression not allowed in type"))

-- Reparse an expression on the left side of an '=' into either a pattern
-- (for a let) or a function declaraction (for a def).
lefthandside :: Loc Exp -> P (Either Pattern (Loc Var, [Pattern]))
lefthandside (Loc _ (ExpLoc l e)) = lefthandside (Loc l e)
lefthandside (Loc l (Apply e el)) | Just v <- unVar l e, not (isCons (unLoc v)) = do
  pl <- mapM (patternExp l) el
  return $ Right (v,pl)
lefthandside (Loc l (Ops (OpBin v o1 o2))) | not (isCons v) = do
  p1 <- patternOps l o1
  p2 <- patternOps l o2
  return $ Right (Loc l v, map PatOps [p1,p2])
lefthandside (Loc l p) = Left . patLoc . Loc l =.< patternExp l p

unVar :: SrcLoc -> Exp -> Maybe (Loc Var)
unVar l (Var v) = Just (Loc l v)
unVar _ (ExpLoc l e) = unVar l e
unVar _ _ = Nothing

-- Currently, specifications are only allowed to be single lowercase variables
spec :: Loc Exp -> P (Loc Var)
spec (Loc l e) | Just v <- unVar l e = return v
spec (Loc l e) = parseError (ParseError l ("only variables are allowed in top level type specifications, not '"++show (pretty e)++"'"))

-- Reparse an expression into a constructor
constructor :: Loc Exp -> P (Loc CVar,[TypeSet])
constructor (Loc _ (ExpLoc l e)) = constructor (Loc l e)
constructor (Loc l e) | Just v <- unVar l e, isCons (unLoc v) = return (v,[])
constructor (Loc l (Apply e el)) | Just v <- unVar l e, isCons (unLoc v) = do
  tl <- mapM (typeExp l) el
  return (v,tl)
constructor (Loc l (Ops (OpBin v (OpAtom e1) (OpAtom e2)))) | isCons v = do
  t1 <- typeExp l e1
  t2 <- typeExp l e2
  return (Loc l v,[t1,t2])
constructor (Loc l e) = parseError (ParseError l ("invalid constructor expression '"++show (pretty e)++"' (must be <constructor> <args>... or equivalent)"))

}
