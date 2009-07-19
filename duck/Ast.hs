{-# LANGUAGE PatternGuards, FlexibleInstances #-}
-- | Duck Abstract Syntax Tree

module Ast
  ( Prog
  , Decl(..)
  , Exp(..)
  , Pattern(..)
  , opsExp
  , opsPattern
  ) where

import Var
import Type
import SrcLoc
import ParseOps
import Pretty
import ParseMonad
import Text.PrettyPrint
import Data.List

type Prog = [Loc Decl]

data Decl
  = SpecD Var TypeSet
  | DefD Var [Pattern] Exp
  | LetD Pattern Exp
  | Data CVar [Var] [(CVar,[TypeSet])]
  | Infix PrecFix [Var]
  deriving Show

data Exp
  = Def Var [Pattern] Exp Exp
  | Let Pattern Exp Exp
  | Lambda [Pattern] Exp
  | Apply Exp [Exp]
  | Var Var
  | Int Int
  | List [Exp]
  | Ops (Ops Exp)
  | TypeCheck Exp TypeSet
  | Case Exp [(Pattern,Exp)]
  | If Exp Exp Exp
  | ExpLoc SrcLoc Exp
  deriving Show

data Pattern
  = PatAny
  | PatVar Var
  | PatCons CVar [Pattern]
  | PatOps (Ops Pattern)
  | PatType Pattern TypeSet
  deriving Show

-- Pretty printing

opsExp :: Ops Exp -> Exp
opsExp (OpAtom a) = a
opsExp (OpUn (V "-") a) = Apply (Var (V "negate")) [opsExp a]
opsExp (OpUn op _) = parseThrow (show (pretty op)++" cannot be used as a prefix operator (the only valid prefix operator is \"-\")")
opsExp (OpBin o l r) = Apply (Var o) [opsExp l, opsExp r]

opsPattern :: Ops Pattern -> Pattern
opsPattern (OpAtom a) = a
opsPattern (OpUn _ _) = parseThrow "unary operator in pattern"
opsPattern (OpBin o l r) = PatCons o [opsPattern l, opsPattern r]

instance Pretty (Loc Decl) where
  pretty' (Loc _ d) = pretty' d

instance Pretty Decl where
  pretty (SpecD f t) =
    pretty f <+> text "::" <+> pretty t
  pretty (DefD f args e) =
    pretty f <+> prettylist args <+> equals $$ nest 2 (guard 0 e)
  pretty (LetD p e) =
    pretty p <+> equals <+> pretty e
  pretty (Data t args []) =
    text "data" <+> pretty t <+> prettylist args
  pretty (Data t args (hd:tl)) =
    text "data" <+> pretty t <+> prettylist args $$ nest 2 (vcat (
      (equals <+> f hd) : map (\x -> text "|" <+> f x) tl))
    where f (c,args) = pretty c <+> prettylist args
  pretty (Infix (p,d) syms) =
    text s <+> int p <+> hcat (intersperse (text ", ") (map (\ (V s) -> text s) syms))
    where
    s = case d of
      LeftFix -> "infixl"
      RightFix -> "infixr"
      NonFix -> "infix"

instance Pretty Exp where
  pretty' (Let p e body) = (0,
    text "let" <+> pretty p <+> equals <+> guard 0 e <+> text "in"
      $$ (guard 0 body))
  pretty' (Def f args e body) = (0,
    text "let" <+> pretty f <+> prettylist args <+> equals
      $$ nest 2 (guard 0 e) <+> text "in" $$ (guard 0 body))
  pretty' (Lambda args e) = (5,
    text "\\" <> prettylist args <+> text "->" <+> guard 5 e)
  pretty' (Apply (Var v) [e1, e2]) | Just prec <- precedence v =
    let V s = v in
    (prec, (guard prec e1) <+> text s <+> (guard (prec+1) e2) )
  pretty' (Apply (Var c) el) | Just n <- tuplelen c, n == length el = (1,
    hcat $ intersperse (text ", ") $ map (guard 2) el)
  pretty' (Apply e el) = (50, guard 51 e <+> prettylist el)
  pretty' (Var v) = pretty' v
  pretty' (Int i) = pretty' i
  pretty' (List el) = (100,
    lbrack <> hcat (intersperse (text ", ") $ map (guard 2) el) <> rbrack)
  pretty' (Ops o) = pretty' o
  pretty' (Case e cases) = (0,
    text "case" <+> pretty e <+> text "of" $$ nest 2 (
      vjoin '|' (map (\ (p,e) -> pretty p <+> text "->" <+> pretty e) cases)))
  pretty' (TypeCheck e t) = (2, guard 2 e <+> text "::" <+> guard 60 t)
  pretty' (If c e1 e2) = (0,
    text "if" <+> pretty c <+> text "then" <+> pretty e1 <+> text "else" <+> pretty e2)
  pretty' (ExpLoc _ e) = pretty' e

instance Pretty Pattern where
  pretty' (PatAny) = pretty' '_'
  pretty' (PatVar v) = pretty' v
  pretty' (PatCons c []) = pretty' c
  pretty' (PatCons c pl) | istuple c = (1, hcat $ intersperse (text ", ") $ map (guard 2) pl)
  pretty' (PatCons c pl) = (3, pretty c <+> prettylist pl)
  pretty' (PatOps o) = pretty' o
  pretty' (PatType p t) = (2, guard 2 p <+> text "::" <+> guard 0 t)
