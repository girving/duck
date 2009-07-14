{-# LANGUAGE PatternGuards #-}
-- | Duck Intermediate Representation

module Ir 
  ( Decl(..)
  , Exp(..)
  , Binop(..)
  , PrimIO(..)
  , prog
  , binopString
  ) where

import Var
import Type
import Data.Maybe
import qualified Ast
import qualified Data.Set as Set
import qualified Data.Map as Map

import Util
import Pretty
import ParseOps
import SrcLoc
import Text.PrettyPrint
import Data.List
import Data.Either
import Data.Function
import qualified Data.Foldable as Fold
import GHC.Exts

data Decl
  = LetD Var Exp
  | LetM [Var] Exp
  | Over Var TypeSet Exp
  | Data CVar [Var] [(CVar, [TypeSet])]
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
    -- Monadic IO
  | Bind Var Exp Exp
  | Return Exp
  | PrimIO PrimIO [Exp]
  | ExpLoc SrcLoc Exp
  deriving Show

data Binop
  = IntAddOp
  | IntSubOp
  | IntMulOp
  | IntDivOp
  | IntEqOp
  | IntLessOp
  deriving Show

data PrimIO
  = ExitFailure
  | TestAll
  deriving Show

-- Ast to IR conversion

data Env = Env 
  { envPrecs :: PrecEnv
  }

prog_vars :: Ast.Prog -> InScopeSet
prog_vars = foldl' decl_vars Set.empty

decl_vars :: InScopeSet -> Ast.Decl -> InScopeSet
decl_vars s (Ast.DefD v _ _ _) = Set.insert v s 
decl_vars s (Ast.LetD p _) = pattern_vars s p
decl_vars s (Ast.Data _ _ _) = s
decl_vars s (Ast.Infix _ _) = s

pattern_vars :: InScopeSet -> Ast.Pattern -> InScopeSet
pattern_vars s Ast.PatAny = s
pattern_vars s (Ast.PatVar v) = Set.insert v s
pattern_vars s (Ast.PatCons _ pl) = foldl' pattern_vars s pl
pattern_vars s (Ast.PatOps o) = Fold.foldl' pattern_vars s o
pattern_vars s (Ast.PatType _ _) = s

prog_precs :: Ast.Prog -> PrecEnv
prog_precs = foldl' set_precs Map.empty where
  -- TODO: error on duplicates
  set_precs s (Ast.Infix p vl) = foldl' (\s v -> Map.insert v p s) s vl
  set_precs s _ = s

prog :: [Ast.Decl] -> [Decl]
prog decls = catMaybes $ map (decl (Env precs) vars) decls where
  vars = prog_vars decls
  precs = prog_precs decls

decl :: Env -> InScopeSet -> Ast.Decl -> Maybe Decl
decl env s (Ast.DefD f Nothing args body) = Just $ LetD f (expr env s (Ast.Lambda args body))
decl env s (Ast.DefD f (Just t) args body) = Just $ Over f t (expr env s (Ast.Lambda args body))
decl env s (Ast.LetD Ast.PatAny e) = Just $ LetD ignored (expr env s e)
decl env s (Ast.LetD (Ast.PatVar v) e) = Just $ LetD v (expr env s e)
decl env s (Ast.LetD p e) = Just d where
  d = case vars of
    [v] -> LetD v (m (expr env s e) (Var v))
    vl -> LetM vl (m (expr env s e) (Cons (tuple vars) (map Var vars)))
  vars = Set.toList (pattern_vars Set.empty p)
  (_,_,m) = match env s p
decl _ _ (Ast.Data t args cons) = Just $ Data t args cons
decl _ _ (Ast.Infix _ _) = Nothing

expr :: Env -> InScopeSet -> Ast.Exp -> Exp
expr _ _ (Ast.Int i) = Int i
expr _ _ (Ast.Var v) = Var v
expr env s (Ast.Lambda args e) = foldr Lambda (m (map Var vl) (expr env s' e)) vl where
  (vl, s', m) = matches env s args
expr env s (Ast.Apply f args) = foldl' Apply (expr env s f) (map (expr env s) args)
expr env s (Ast.Let p e c) = m (expr env s e) (expr env s' c) where
  (_,s',m) = match env s p
expr env s (Ast.Def f args body c) = Let f lambda (expr env sc c) where
  (vl, s', m) = matches env s args
  lambda = foldr Lambda (m (map Var vl) (expr env s' body)) vl
  sc = Set.insert f s
expr env s (Ast.Case e cl) = cases env s (expr env s e) cl
expr env s (Ast.Ops o) = expr env s $ Ast.opsExp $ sortOps (envPrecs env) o
expr env s (Ast.TypeCheck e _) = expr env s e
expr env s (Ast.List el) = foldr (\a b -> Cons (V ":") [a,b]) (Cons (V "[]") []) (map (expr env s) el)
expr env s (Ast.If c e1 e2) = Apply (Apply (Apply (Var (V "if")) (expr env s c)) (expr env s e1)) (expr env s e2)
expr env s (Ast.ExpLoc l e) = ExpLoc l $ expr env s e

-- |match processes a single pattern into an input variable, a new in-scope set,
-- and a transformer that converts an input expression and a result expression
-- into new expression representing the match
match :: Env -> InScopeSet -> Ast.Pattern -> (Var, InScopeSet, Exp -> Exp -> Exp)
match _ s Ast.PatAny = (ignored, s, match_helper ignored)
match _ s (Ast.PatVar v) = (v, Set.insert v s, match_helper v)
match env s (Ast.PatType p _) = match env s p
match env s (Ast.PatOps o) = match env s $ Ast.opsPattern $ sortOps (envPrecs env) o
match env s (Ast.PatCons c args) = (x, s', m) where
  x = fresh s
  (vl, s', ms) = matches env s args
  m em er = Case em [(c, vl, ms (map Var vl) er)] Nothing

match_helper v em er = case em of
  Var v' | v == v' -> er
  _ -> Let v em er

-- in spirit, matches = fold match
matches :: Env -> InScopeSet -> [Ast.Pattern] -> ([Var], InScopeSet, [Exp] -> Exp -> Exp)
matches env s pl = foldr f ([],s,\[] -> id) pl where
  f p (vl,s,m) = (v:vl, s', \ (e:el) -> m' e . m el) where
    (v,s',m') = match env s p

-- |cases turns a multilevel pattern match into iterated single level pattern match by
--   (1) partitioning the cases by outer element,
--   (2) performing the outer match, and
--   (3) iteratively matching the components returned in the outer match
-- Part (3) is handled by building up a stack of unprocessed expressions and an associated
-- set of pattern stacks, and then iteratively reducing the set of possibilities.
cases :: Env -> InScopeSet -> Exp -> [(Ast.Pattern, Ast.Exp)] -> Exp
cases env s e arms = reduce s [e] (map (\ (p,e) -> p :. Base e) arms) where 

  -- reduce takes n unmatched expressions and a list of n-tuples (lists) of patterns, and
  -- iteratively reduces the list of possibilities by matching each expression in turn.  This is
  -- used to process the stack of unmatched patterns that build up as we expand constructors.
  reduce :: InScopeSet -> [Exp] -> [Stack Ast.Pattern Ast.Exp] -> Exp
  reduce s [] (Base e:_) = expr env s e -- no more patterns to match, so just pick the first possibility
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
      [alt] -> (c,vl',m ex (expr env s' e)) where -- single alternative, use matches
        (pl,e) = splitStack alt
        (vl,s',m) = matches env s pl
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
  separate (Ast.PatOps o :. e) = separate ((Ast.opsPattern $ sortOps (envPrecs env) o) :. e)
  separate (Ast.PatCons c pl :. e) = Left ((c, length pl), pl++.e)
  separate (Base _) = undefined -- will never happen, since here the stack is nonempty

-- Pretty printing

instance Pretty Decl where
  pretty (LetD v e) =
    text "let" <+> pretty v <+> equals <+> nest 2 (pretty e)
  pretty (LetM vl e) =
    text "let" <+> hcat (intersperse (text ", ") (map pretty vl)) <+> equals <+> nest 2 (pretty e)
  pretty (Over v t e) =
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
    (e, el) -> (50, guard 50 e <+> prettylist el)
    where apply (Apply e a) al = apply e (a:al) 
          apply e al = (e,al)
  pretty' (Let v e body) = (0,
    text "let" <+> pretty v <+> equals <+> guard 0 e <+> text "in"
      $$ guard 0 body)
  pretty' (Cons (V ":") [h,t]) | Just t' <- extract t = (100,
    brackets (hcat (intersperse (text ", ") $ map (guard 2) (h : t')))) where
    extract (Cons (V "[]") []) = Just []
    extract (Cons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
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
  pretty' (Bind v e1 e2) = (6,
    pretty v <+> text "<-" <+> guard 0 e1 $$ guard 0 e2)
  pretty' (Return e) = (6, text "return" <+> guard 7 e)
  pretty' (PrimIO p []) = pretty' p
  pretty' (PrimIO p args) = (50, guard 50 p <+> prettylist args)
  -- pretty' (ExpLoc l e) = fmap (text "{-@" <+> text (show l) <+> text "-}" <+>) $ pretty' e
  pretty' (ExpLoc _ e) = pretty' e

instance Pretty PrimIO where
  pretty' p = (100, text (show p))

binopPrecedence :: Binop -> Int
binopPrecedence op = case op of
  IntAddOp -> 20
  IntSubOp -> 20
  IntMulOp -> 30
  IntDivOp -> 30
  IntEqOp -> 10
  IntLessOp -> 10

binopString :: Binop -> String
binopString op = case op of
  IntAddOp -> "+"
  IntSubOp -> "-"
  IntMulOp -> "*"
  IntDivOp -> "/"
  IntEqOp -> "=="
  IntLessOp -> "<"
