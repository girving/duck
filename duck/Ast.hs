{-# LANGUAGE PatternGuards, FlexibleInstances #-}
-- | Duck Abstract Syntax Tree

module Ast
  ( Prog
  , Decl(..)
  , Exp(..)
  , Pattern(..)
  , imports
  , opsExp
  , opsPattern
  ) where

import Var
import Type
import SrcLoc
import ParseOps
import Pretty
import ParseMonad
import Data.List
import Data.Maybe

type Prog = [Loc Decl]

data Decl
  = SpecD (Loc Var) TypeSet
  | DefD (Loc Var) [Pattern] Exp
  | LetD Pattern Exp
  | Data (Loc CVar) [Var] [(Loc CVar,[TypeSet])]
  | Infix PrecFix [Var]
  | Import Var
  deriving Show

data Exp
  = Def Var [Pattern] Exp Exp
  | Let Pattern Exp Exp
  | Lambda [Pattern] Exp
  | Apply Exp [Exp]
  | Var Var
  | Int Int
  | Chr Char
  | Any
  | List [Exp]
  | Ops (Ops Exp)
  | Spec Exp TypeSet
  | Case Exp [(Pattern,Exp)]
  | If Exp Exp Exp
  | ExpLoc SrcLoc Exp
  deriving Show

data Pattern
  = PatAny
  | PatVar Var
  | PatCons CVar [Pattern]
  | PatList [Pattern]
  | PatOps (Ops Pattern)
  | PatLambda [Pattern] Pattern
  | PatSpec Pattern TypeSet
  | PatLoc SrcLoc Pattern
  deriving Show

imports :: Prog -> [String]
imports = mapMaybe imp where
  imp (Loc _ (Import (V v))) = Just v
  imp _ = Nothing

-- Pretty printing

opsExp :: Ops Exp -> Exp
opsExp (OpAtom a) = a
opsExp (OpUn (V "-") a) = Apply (Var (V "negate")) [opsExp a]
opsExp (OpUn op _) = parseThrow (pshow op++" cannot be used as a prefix operator (the only valid prefix operator is \"-\")")
opsExp (OpBin o l r) = Apply (Var o) [opsExp l, opsExp r]

opsPattern :: Ops Pattern -> Pattern
opsPattern (OpAtom a) = a
opsPattern (OpUn _ _) = parseThrow "unary operator in pattern"
opsPattern (OpBin o l r) = PatCons o [opsPattern l, opsPattern r]

instance Pretty Decl where
  pretty (SpecD f t) =
    pretty f <+> pretty "::" <+> pretty t
  pretty (DefD f args e) =
    pretty f <+> prettylist args <+> equals $$ nest 2 (guard 0 e)
  pretty (LetD p e) =
    pretty p <+> equals <+> pretty e
  pretty (Data t args []) =
    pretty "data" <+> pretty t <+> prettylist args
  pretty (Data t args (hd:tl)) =
    pretty "data" <+> pretty t <+> prettylist args $$ nest 2 (vcat (
      (equals <+> f hd) : map (\x -> pretty "|" <+> f x) tl))
    where f (c,args) = pretty c <+> prettylist args
  pretty (Infix (p,d) syms) =
    pretty s <+> pretty p <+> hcat (intersperse (pretty ", ") (map (\ (V s) -> pretty s) syms))
    where
    s = case d of
      LeftFix -> "infixl"
      RightFix -> "infixr"
      NonFix -> "infix"
  pretty (Import v) =
    pretty "import" <+> pretty v

instance Pretty Exp where
  pretty' (Spec e t) = (0, guard 1 e <+> pretty "::" <+> guard 60 t)
  pretty' (Let p e body) = (1,
    pretty "let" <+> pretty p <+> equals <+> guard 0 e <+> pretty "in"
      $$ (guard 0 body))
  pretty' (Def f args e body) = (1,
    pretty "let" <+> pretty f <+> prettylist args <+> equals
      $$ nest 2 (guard 0 e) <+> pretty "in" $$ (guard 0 body))
  pretty' (Case e cases) = (1,
    pretty "case" <+> pretty e <+> pretty "of" $$ nest 2 (
      vjoin '|' (map (\ (p,e) -> pretty p <+> pretty "->" <+> pretty e) cases)))
  pretty' (If c e1 e2) = (1,
    pretty "if" <+> pretty c <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2)
  pretty' (Lambda pl e) = (1, hsep (map (\p -> guard 2 p <+> pretty "->") pl) <+> guard 1 e)
  pretty' (Apply (Var v) [e1, e2]) | Just prec <- precedence v =
    let V s = v in
    (prec, (guard prec e1) <+> pretty s <+> (guard (prec+1) e2) )
  pretty' (Apply (Var c) el) | Just n <- tuplelen c, n == length el = (2,
    hcat $ intersperse (pretty ", ") $ map (guard 3) el)
  pretty' (Apply e el) = (50, guard 51 e <+> prettylist el)
  pretty' (Var v) = pretty' v
  pretty' (Int i) = pretty' i
  pretty' (Chr c) = (100, pretty (show c))
  pretty' Any = pretty' '_'
  pretty' (List el) = (100,
    brackets $ hcat (intersperse (pretty ", ") $ map (guard 2) el))
  pretty' (Ops o) = pretty' o
  pretty' (ExpLoc _ e) = pretty' e

patToExp :: Pattern -> Exp
patToExp (PatSpec p t) = Spec (patToExp p) t
patToExp (PatCons c pl) = Apply (Var c) (map patToExp pl)
patToExp (PatOps o) = Ops (fmap patToExp o)
patToExp (PatVar v) = Var v
patToExp (PatList pl) = List (map patToExp pl)
patToExp (PatLambda pl p) = Lambda pl (patToExp p)
patToExp PatAny = Any
patToExp (PatLoc l p) = ExpLoc l (patToExp p)

instance Pretty Pattern where
  pretty' = pretty' . patToExp
