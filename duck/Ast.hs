{-# LANGUAGE PatternGuards, FlexibleInstances, TypeSynonymInstances #-}
-- | Duck Abstract Syntax Tree
--
-- The parser ("Parse") turns the string contents of a single file into a 'Prog'

module Ast
  ( Prog
  , Decl(..)
  , Exp(..)
  , Pattern(..)
  , imports
  , opsExp
  , opsPattern
  ) where

import Data.List
import Data.Maybe

import Var
import Type
import SrcLoc
import Stage
import ParseOps
import Pretty

-- |An entire file is just a list of top-level declarations, where the locations refer to the whole declaration, body and all
type Prog = [Loc Decl]

-- |Top-level declaration
data Decl
  = SpecD !(Loc Var) !TypePat           -- ^ Type declaration (for overloads): @VAR :: TYPE@
  | DefD !(Loc Var) [Pattern] Exp       -- ^ Function definition with arguments: @VAR PATs = EXP@
  | LetD !Pattern Exp                   -- ^ Global definition without arguments: @PAT = EXP@
  | Data !(Loc CVar) [Var] [(Loc CVar,[TypePat])] -- ^ Datatype declaration: @data CVAR VARs = { CVAR TYPEs ; ... }@
  | Infix !PrecFix [Var]                -- ^ Fixity declaration: @infix[lr] PREC VARs@
  | Import !Var                         -- ^ Import directive: @import VAR@
  deriving Show

-- |Expression
-- Patterns and types are also parsed into these before being converted to 'Pattern' or 'TypePat' in "Parse"
data Exp
  = Def !Var [Pattern] Exp Exp          -- ^ Local function definition with arguments: @let VAR PATs = EXP in EXP@
  | Let !Pattern Exp Exp                -- ^ Local variable definition: @let PAT = EXP in EXP@
  | Lambda [Pattern] Exp                -- ^ @PAT1 -> PAT2 ... -> EXP@
  | Apply Exp [Exp]                     -- ^ Application: @EXP EXPs@
  | Var !Var
  | Int !Int
  | Chr !Char
  | Any                                 -- ^ Magic underscore variable: @_@
  | List [Exp]                          -- ^ List: @[EXP1,...]@
  | Ops !(Ops Exp)
  | Equals !Var Exp                     -- ^ @(VAR = EXP)@, only for PatAs
  | Spec Exp !TypePat                   -- ^ Type specification: @EXP :: TYPE@
  | Case Exp [(Pattern,Exp)]            -- ^ @case EXP of { PAT -> EXP ; ... }@
  | If Exp Exp Exp                      -- ^ @if EXP then EXP else EXP@
  | ExpLoc SrcLoc !Exp                  -- ^ Meta source location information, inserted at almost every level
  deriving Show

-- |Pattern
-- For the most part, each constructor here is converted from its non-Pat equivalent in 'Exp'.
data Pattern
  = PatAny
  | PatVar !Var
  | PatCons !CVar [Pattern]
  | PatList [Pattern]
  | PatOps !(Ops Pattern)
  | PatLambda [Pattern] !Pattern
  | PatAs !Var !Pattern
  | PatSpec !Pattern !TypePat
  | PatLoc SrcLoc !Pattern
  deriving Show

-- |List of 'Import' directives
imports :: Prog -> [String]
imports = mapMaybe imp where
  imp (Loc _ (Import (V v))) = Just v
  imp _ = Nothing

-- |Convert an 'Ops' expression into its 'Apply' equivalents, without applying any precedences (see "ParseOps")
opsExp :: SrcLoc -> Ops Exp -> Exp
opsExp _ (OpAtom a) = a
opsExp loc (OpUn (V "-") a) = Apply (Var (V "negate")) [opsExp loc a]
opsExp loc (OpUn op _) = fatal $ stageMsg StageParse loc $ quoted op <+> "cannot be used as a prefix operator (the only valid prefix operator is" <+> quoted "-" <> ")"
opsExp loc (OpBin o l r) = Apply (Var o) [opsExp loc l, opsExp loc r]

-- |Convert 'PatOps' pattern into its 'PatCons' equivalents, without applying any precedences (see "ParseOps")
opsPattern :: SrcLoc -> Ops Pattern -> Pattern
opsPattern _ (OpAtom a) = a
opsPattern loc (OpUn _ _) = fatal $ stageMsg StageParse loc $ "unary operator in pattern"
opsPattern loc (OpBin o l r) = PatCons o [opsPattern loc l, opsPattern loc r]

instance HasVar Exp where
  var = Var
  unVar (Var v) = Just v
  unVar Any = Just ignored
  unVar (ExpLoc _ e) = unVar e
  unVar (Ops e) = unVar e
  unVar _ = Nothing

instance HasVar Pattern where
  var = PatVar
  unVar (PatVar v) = Just v
  unVar PatAny = Just ignored
  unVar (PatLoc _ p) = unVar p
  unVar (PatOps p) = unVar p
  unVar _ = Nothing

-- Pretty printing

instance Pretty Decl where
  pretty (SpecD f t) =
    pretty f <+> pretty "::" <+> pretty t
  pretty (DefD f args e) =
    nested (pretty f <+> prettylist args <+> equals) (guard 0 e)
  pretty (LetD p e) =
    pretty p <+> equals <+> pretty e
  pretty (Data t args []) =
    pretty "data" <+> pretty t <+> prettylist args
  pretty (Data t args (hd:tl)) =
    nested (pretty "data" <+> pretty t <+> prettylist args) (vcat (
      (equals <+> f hd) : map (\x -> pretty "|" <+> f x) tl))
    where f (c,args) = pretty c <+> prettylist args
  pretty (Infix pf syms) =
    pretty pf <+> hcat (intersperse (pretty ", ") (map (\ (V s) -> pretty s) syms))
  pretty (Import v) =
    pretty "import" <+> pretty v

instance Pretty Prog where
  pretty = vcat

instance Pretty Exp where
  pretty' (Spec e t) = (0, guard 1 e <+> pretty "::" <+> guard 60 t)
  pretty' (Let p e body) = (1,
    pretty "let" <+> pretty p <+> equals <+> guard 0 e <+> pretty "in"
      $$ (guard 0 body))
  pretty' (Def f args e body) = (1,
    nestedPunct '=' ("let" <+> f <+> prettylist args) $
      guard 0 e <+> "in" $$ guard 0 body)
  pretty' (Case e cases) = (1,
    nested (pretty "case" <+> pretty e <+> pretty "of") $ 
      vcat (map (\ (p,e) -> pretty p <+> pretty "->" <+> pretty e) cases))
  pretty' (If c e1 e2) = (1,
    pretty "if" <+> pretty c <+> pretty "then" <+> pretty e1 <+> pretty "else" <+> pretty e2)
  pretty' (Lambda pl e) = (1, hsep (map (\p -> guard 2 p <+> pretty "->") pl) <+> guard 1 e)
  pretty' (Apply (Var v) [e1, e2]) | Just prec <- precedence v =
    let V s = v in
    (prec, (guard prec e1) <+> pretty s <+> (guard (prec+1) e2) )
  pretty' (Apply (Var c) el) | Just n <- tupleLen c, n == length el = (2,
    punctuate ',' $ map (guard 3) el)
  pretty' (Apply e el) = (50, guard 51 e <+> prettylist el)
  pretty' (Var v) = pretty' v
  pretty' (Int i) = pretty' i
  pretty' (Chr c) = (100, pretty (show c))
  pretty' Any = pretty' '_'
  pretty' (List el) = pretty' $
    brackets $ (punctuate ',' $ map (guard 2) el)
  pretty' (Ops o) = pretty' o
  pretty' (Equals v e) = (1, pretty v <+> equals <+> guard 0 e)
  pretty' (ExpLoc _ e) = pretty' e

patToExp :: Pattern -> Exp
patToExp (PatAs v p) = Equals v (patToExp p)
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
