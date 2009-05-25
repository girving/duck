{-# LANGUAGE PatternGuards #-}
-- Duck Intermediate Representation

module Ir 
  ( Decl(..)
  , Exp(..)
  , Binop(..)
  , prog
  , binopString
  ) where

import Var
import Type
import Data.Maybe
import qualified Ast
import qualified Data.Set as Set

import Util
import Pretty
import Text.PrettyPrint
import Data.List
import Data.Either
import Data.Function
import GHC.Exts

data Decl
  = LetD Var Exp
  | LetMD [Var] Exp
  | OverD Var Type Exp
  | Data CVar [Var] [(CVar, [Type])]
  deriving Show

data Exp
  = Int Int
  | Var Var
  | Lambda Var Exp
  | Apply Exp Exp
  | Let Var Exp Exp
  | Cons CVar [Exp]
  | Case Exp [(CVar, [Var], Exp)] (Maybe (Var,Exp))
  | Binop Binop Exp Exp
  deriving Show

data Binop
  = IntAddOp
  | IntSubOp
  | IntMulOp
  | IntDivOp
  deriving Show

-- Ast to IR conversion

prog_vars :: [Ast.Decl] -> InScopeSet
prog_vars = foldl decl_vars Set.empty

decl_vars :: InScopeSet -> Ast.Decl -> InScopeSet
decl_vars s (Ast.DefD v _ _ _) = Set.insert v s 
decl_vars s (Ast.LetD p _) = pattern_vars s p
decl_vars s (Ast.Data _ _ _) = s
decl_vars s (Ast.Infix _ _ _) = s

pattern_vars :: InScopeSet -> Ast.Pattern -> InScopeSet
pattern_vars s Ast.PatAny = s
pattern_vars s (Ast.PatVar v) = Set.insert v s
pattern_vars s (Ast.PatCons _ pl) = foldl pattern_vars s pl
pattern_vars s (Ast.PatType _ _) = s

prog :: [Ast.Decl] -> [Decl]
prog decls = catMaybes $ map (decl (prog_vars decls)) decls

decl :: InScopeSet -> Ast.Decl -> Maybe Decl
decl s (Ast.DefD f Nothing args body) = Just $ LetD f (expr s (Ast.Lambda args body))
decl s (Ast.DefD f (Just t) args body) = Just $ OverD f t (expr s (Ast.Lambda args body))
decl s (Ast.LetD Ast.PatAny e) = Just $ LetD ignored (expr s e)
decl s (Ast.LetD (Ast.PatVar v) e) = Just $ LetD v (expr s e)
decl s (Ast.LetD p e) = Just d where
  d = case vars of
    [v] -> LetD v (m (expr s e) (Var v))
    vl -> LetMD vl (m (expr s e) (Cons (tuple vars) (map Var vars)))
  vars = Set.toList (pattern_vars Set.empty p)
  (_,_,m) = match s p
decl _ (Ast.Data t args cons) = Just $ Data t args cons
decl _ (Ast.Infix _ _ _) = Nothing

expr :: InScopeSet -> Ast.Exp -> Exp
expr _ (Ast.Int i) = Int i
expr _ (Ast.Var v) = Var v
expr s (Ast.Lambda args e) = foldr Lambda (m (map Var vl) (expr s' e)) vl where
  (vl, s', m) = matches s args
expr s (Ast.Apply f args) = foldl Apply (expr s f) (map (expr s) args)
expr s (Ast.Let p e c) = m (expr s e) (expr s' c) where
  (_,s',m) = match s p
expr s (Ast.Def f args body c) = Let f lambda (expr sc c) where
  (vl, s', m) = matches s args
  lambda = foldr Lambda (m (map Var vl) (expr s' body)) vl
  sc = Set.insert f s
expr s (Ast.Case e cl) = cases s (expr s e) cl
expr s (Ast.TypeCheck e _) = expr s e
expr s (Ast.List el) = foldr (\a b -> Cons (V ":") [a,b]) (Var (V "[]")) (map (expr s) el)

-- match processes a single pattern into an input variable, a new in-scope set,
-- and a transformer that converts an input expression and a result expression
-- into new expression representing the match
match :: InScopeSet -> Ast.Pattern -> (Var, InScopeSet, Exp -> Exp -> Exp)
match s Ast.PatAny = (ignored, s, match_helper ignored)
match s (Ast.PatVar v) = (v, Set.insert v s, match_helper v)
match s (Ast.PatType p _) = match s p
match s (Ast.PatCons c args) = (x, s', m) where
  x = fresh s
  (vl, s', ms) = matches s args
  m em er = Case em [(c, vl, ms (map Var vl) er)] Nothing

match_helper v em er = case em of
  Var v' | v == v' -> er
  _ -> Let v em er

-- in spirit, matches = fold match
matches :: InScopeSet -> [Ast.Pattern] -> ([Var], InScopeSet, [Exp] -> Exp -> Exp)
matches s pl = foldr f ([],s,\[] -> id) pl where
  f p (vl,s,m) = (v:vl, s', \ (e:el) -> m' e . m el) where
    (v,s',m') = match s p

-- cases turns a multilevel pattern match into iterated single level pattern match by
--   (1) partitioning the cases by outer element,
--   (2) performing the outer match, and
--   (3) iteratively matching the components returned in the outer match
-- Part (3) is handled by building up a stack of unprocessed expressions and an associated
-- set of pattern stacks, and then iteratively reducing the set of possibilities.
cases :: InScopeSet -> Exp -> [(Ast.Pattern, Ast.Exp)] -> Exp
cases s e arms = reduce s [e] (map (\ (p,e) -> p :. Base e) arms) where 

  -- reduce takes n unmatched expressions and a list of n-tuples (lists) of patterns, and
  -- iteratively reduces the list of possibilities by matching each expression in turn.  This is
  -- used to process the stack of unmatched patterns that build up as we expand constructors.
  reduce :: InScopeSet -> [Exp] -> [Stack Ast.Pattern Ast.Exp] -> Exp
  reduce s [] (Base e:_) = expr s e -- no more patterns to match, so just pick the first possibility
  reduce _ [] _ = undefined -- there will always be at least one possibility, so this never happens
  reduce s (e:rest) alts = Case e (map cons groups) fallback where

    -- group alternatives by toplevel tag (along with arity)
    -- note: In future, the arity might be looked up in an environment
    -- (or maybe not, if constructors are overloaded based on arity?)
    groups = groupPairs conses
    (conses,others) = partitionEithers (map separate alts)

    -- cons processes each case of the toplevel match
    -- If only one alternative remains, we break out of the 'reduce' recursion and switch
    -- to 'matches', which avoids trivial matches of the form "case v of v -> ..."
    cons ((c,arity),alts') = case alts' of
      [alt] -> (c,vl',m ex (expr s' e)) where -- single alternative, use matches
        (pl,e) = splitStack alt
        (vl,s',m) = matches s pl
        vl' = take arity vl
        ex = (map Var vl') ++ rest
      _ -> (c,vl,ex) where -- many alernatives, use reduce
        (s',vl) = freshVars s arity
        ex = reduce s' (map Var vl ++ rest) alts'

    fallback = case others of
      [] -> Nothing
      (v,e):_ -> Just (v,(reduce (Set.insert v s) rest [e]))

  -- peel off the outer level of the first pattern, and separate into conses and defaults
  separate :: Stack Ast.Pattern Ast.Exp -> Either ((Var,Int), Stack Ast.Pattern Ast.Exp) (Var, Stack Ast.Pattern Ast.Exp)
  separate (Ast.PatAny :. e) = Right (ignored,e)
  separate (Ast.PatVar v :. e) = Right (v,e)
  separate (Ast.PatType p _ :. e) = separate (p:.e)
  separate (Ast.PatCons c pl :. e) = Left ((c, length pl), pl++.e)
  separate (Base _) = undefined -- will never happen, since here the stack is nonempty

-- Pretty printing

instance Pretty Decl where
  pretty (LetD v e) =
    text "let" <+> pretty v <+> equals <+> nest 2 (pretty e)
  pretty (LetMD vl e) =
    text "let" <+> hcat (intersperse (text ", ") (map pretty vl)) <+> equals <+> nest 2 (pretty e)
  pretty (OverD v t e) =
    text "over" <+> pretty t $$
    text "let" <+> pretty v <+> equals <+> nest 2 (pretty e)
  pretty (Data t args cons) =
    pretty (Ast.Data t args cons)

instance Pretty Exp where
  pretty' (Int i) = pretty' i
  pretty' (Var v) = pretty' v
  pretty' (Lambda v e) = (5,
    text "\\" <> pretty v <+> text "->" <+> nest 2 (guard 5 e))
  pretty' (Apply e1 e2) = case (apply e1 [e2]) of
    (Var v, [e1,e2]) | Just prec <- precedence v -> (prec,
      let V s = v in
      (guard prec e1) <+> text s <+> (guard (prec+1) e2))
    (Var c, el) | Just n <- tuplelen c, n == length el -> (1,
      hcat $ intersperse (text ", ") $ map (guard 2) el)
    (e, el) -> (50, guard 50 e <+> hsep (map (guard 51) el))
    where apply (Apply e a) al = apply e (a:al) 
          apply e al = (e,al)
  pretty' (Let v e body) = (0,
    text "let" <+> pretty v <+> equals <+> guard 0 e <+> text "in"
      $$ guard 0 body)
  pretty' (Cons c args) | istuple c = (1,
    hcat $ intersperse (text ", ") $ map (guard 2) args)
  pretty' (Cons c args) = (50, pretty c <+> sep (map (guard 51) args))
  pretty' (Case e pl d) = (0,
    text "case" <+> pretty e <+> text "of" $$
    vjoin '|' (map arm pl ++ def d)) where
    arm (c, vl, e) 
      | istuple c = hcat (intersperse (text ", ") pvl) <+> end
      | otherwise = pretty c <+> sep pvl <+> end
      where pvl = map pretty vl
            end = text "->" <+> pretty e
    def Nothing = []
    def (Just (v, e)) = [pretty v <+> text "->" <+> pretty e]
  pretty' (Binop op e1 e2) | prec <- binopPrecedence op = (prec,
    guard prec e1 <+> text (binopString op) <+> guard prec e2)

binopPrecedence :: Binop -> Int
binopPrecedence op = case op of
  IntAddOp -> 20
  IntSubOp -> 20
  IntMulOp -> 30
  IntDivOp -> 30

binopString :: Binop -> String
binopString op = case op of
  IntAddOp -> "+"
  IntSubOp -> "-"
  IntMulOp -> "*"
  IntDivOp -> "/"
