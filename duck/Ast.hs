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
  | Char !Char
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
  pretty' (SpecD f t) =
    f <+> "::" <+> t
  pretty' (DefD f args e) =
    nestedPunct '=' (prettyop f args) e
  pretty' (LetD p e) =
    nestedPunct '=' p e
  pretty' (Data t args []) =
    "data" <+> prettyap t args
  pretty' (Data t args l) =
    nested ("data" <+> prettyap t args <+> "of") $
      vcat $ map (\(c,args) -> prettyop c args) l
  pretty' (Infix pf syms) =
    pf <+> punctuate ',' (map (guard (-1)) syms)
  pretty' (Import v) =
    "import" <+> v

instance Pretty Prog where
  pretty' = vcat

instance Pretty Exp where
  pretty' (Spec e t) = 2 #> guard 2 e <+> "::" <+> t
  pretty' (Let p e body) = 1 #>
    "let" <+> p <+> '=' <+> pretty e <+> "in" $$ pretty body
  pretty' (Def f args e body) = 1 #>
    nestedPunct '=' ("let" <+> prettyop f args)
      (pretty e <+> "in" $$ pretty body)
  pretty' (Case e cases) = 1 #>
    nested ("case" <+> pretty e <+> "of")
      (vcat (map (\ (p,e) -> p <+> "->" <+> pretty e) cases))
  pretty' (If c e1 e2) = 1 #>
    "if" <+> pretty c <+> "then" <+> pretty e1 <+> "else" <+> pretty e2
  pretty' (Lambda pl e) = 1 #>
    hsep (map (<+> "->") pl) <+> guard 1 e
  pretty' (Apply e el) = prettyop e el
  pretty' (Var v) = pretty' v
  pretty' (Int i) = pretty' i
  pretty' (Char c) = pretty' (show c)
  pretty' Any = pretty' '_'
  pretty' (List el) = pretty' $ brackets $ 3 #> punctuate ',' el
  pretty' (Ops o) = pretty' o
  pretty' (Equals v e) = 0 #> v <+> '=' <+> guard 0 e
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
