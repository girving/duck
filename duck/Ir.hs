-- Duck Intermediate Representation

module Ir where

import Var
import qualified Ast

import Data.Set (Set)
import qualified Data.Set as Set

import Pretty
import Text.PrettyPrint

data Decl
  = LetD Var Exp
  deriving Show

data Exp
  = Int Int
  | Var Var
  | Lambda Var Exp
  | Apply Exp Exp
  | Let Var Exp Exp
  -- | Case [(Pattern, Exp)]
  deriving Show

-- Ast to IR conversion

type InScopeSet = Set Var

freshen :: InScopeSet -> Var -> Var
freshen inscope v = search v where
  search v | Set.notMember v inscope = v
           | V s <- v = search (V $ s ++ show size)
  size = Set.size inscope

fresh :: InScopeSet -> Var
fresh s = freshen s (V "x")

prog :: [Ast.Decl] -> [Decl]
prog = concatMap decl

decl :: Ast.Decl -> [Decl]
decl (Ast.DefD f args body) = [LetD f (expr (Ast.Lambda args body))]
decl (Ast.LetD Ast.PatAny e) = [LetD (V "_") (expr e)] -- avoid dead code elimination
decl (Ast.LetD (Ast.PatVar v) e) = [LetD v (expr e)]
decl (Ast.LetD p e) = reverse $ match (\v d -> LetD v (expr e) : d) [] p

expr :: Ast.Exp -> Exp
expr (Ast.Int i) = Int i
expr (Ast.Var v) = Var v
expr (Ast.Lambda args e) = foldl (match Lambda) (expr e) args
expr (Ast.Apply f args) = foldl Apply (expr f) (map expr args)
expr (Ast.Let Ast.PatAny e c) = Let (V "_") (expr e) (expr c)
expr (Ast.Let (Ast.PatVar v) e c) = Let v (expr e) (expr c)
expr (Ast.Let p e c) = match (\v e -> Let v e (expr c)) (expr e) p
expr (Ast.Def f args body c) = Let f (expr (Ast.Lambda args body)) (expr c)
expr (Ast.Seq el) = foldl1 (Let (V "_")) (map expr el)

match :: (Var -> a -> a) -> a -> Ast.Pattern -> a
match _ e Ast.PatAny = e
match catch e (Ast.PatVar v) = catch v e
match _ _ _ = error "unimplemented match"

-- Pretty printing

instance Pretty Decl where
  pretty (LetD v e) =
    text "let" <+> pretty v <+> equals <+> nest 2 (pretty e)

instance Pretty Exp where
  pretty' (Int i) = pretty' i
  pretty' (Var v) = pretty' v
  pretty' (Lambda v e) = (5,
    text "\\" <> pretty v <+> text "->" <+> nest 2 (guard 5 e))
  pretty' (Apply (Apply (Var v) e1) e2) | Just prec <- precedence v =
    let V s = v in
    (prec, (guard prec e1) <+> text s <+> (guard (prec+1) e2) )
  pretty' (Apply e1 e2) = (50, guard 50 e1 <+> guard 51 e2)
  pretty' (Let v e body) = (0,
    text "let" <+> pretty v <+> equals <+> guard 0 e <+> text "in"
      $$ guard 0 body)
