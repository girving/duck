{-# LANGUAGE PatternGuards #-}
-- | Duck Intermediate Representation

module Ir 
  ( Decl(..)
  , Exp(..)
  , Binop(..)
  , Prim(..)
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
import Data.Map (Map)

import Util
import Pretty
import ParseOps
import SrcLoc
import Data.List
import Data.Either
import Data.Function
import qualified Data.Foldable as Fold
import GHC.Exts
import Control.Monad hiding (guard)

data Decl
  = LetD !(Loc Var) Exp
  | LetM [Loc Var] Exp
  | Over !(Loc Var) !TypeSet Exp
  | Data !(Loc CVar) [Var] [(Loc CVar, [TypeSet])]
  deriving Show

data Exp
  = ExpLoc SrcLoc !Exp
  | Int !Int
  | Chr !Char
  | Var !Var
  | Lambda !Var Exp
  | Apply Exp Exp
  | Let !Var Exp Exp
  | Cons !CVar [Exp]
  | Case Exp [(CVar, [Var], Exp)] (Maybe (Var,Exp))
  | Prim !Prim [Exp]
  | Spec Exp !TypeSet
    -- Monadic IO
  | Bind !Var Exp Exp
  | Return Exp
  | PrimIO !PrimIO [Exp]
  deriving Show

data Binop
  = IntAddOp
  | IntSubOp
  | IntMulOp
  | IntDivOp
  | IntEqOp
  | IntLTOp
  | IntGTOp
  | IntLEOp
  | IntGEOp
  deriving (Eq, Ord, Show)

data Prim
  = Binop Binop
  | ChrIntOrd
  | IntChrChr
  deriving (Eq, Ord, Show)

data PrimIO
  = ExitFailure
  | IOPutChr
  | TestAll
  deriving (Eq, Ord, Show)

-- Ast to IR conversion

data Pattern
  = PatVar !Var
  | PatCons !CVar [Pattern]
  deriving (Eq, Ord, Show)

data Env = Env 
  { envPrecs :: PrecEnv
  }

-- For now, we use the Either String monad to represent errors during Ast -> Ir conversion.
-- TODO: This should be infused with location information and possibly replaced with a custom monad.
type E = Either String

irError :: String -> E a
irError = fail

prog_vars :: Ast.Prog -> InScopeSet
prog_vars = foldl' decl_vars Set.empty . map unLoc

decl_vars :: InScopeSet -> Ast.Decl -> InScopeSet
decl_vars s (Ast.SpecD (Loc _ v) _) = Set.insert v s 
decl_vars s (Ast.DefD (Loc _ v) _ _) = Set.insert v s 
decl_vars s (Ast.LetD p _) = pattern_vars s p
decl_vars s (Ast.Data _ _ _) = s
decl_vars s (Ast.Infix _ _) = s
decl_vars s (Ast.Import _) = s

pattern_vars :: InScopeSet -> Ast.Pattern -> InScopeSet
pattern_vars s Ast.PatAny = s
pattern_vars s (Ast.PatVar v) = Set.insert v s
pattern_vars s (Ast.PatCons _ pl) = foldl' pattern_vars s pl
pattern_vars s (Ast.PatOps o) = Fold.foldl' pattern_vars s o
pattern_vars s (Ast.PatList pl) = foldl' pattern_vars s pl
pattern_vars s (Ast.PatSpec p _) = pattern_vars s p
pattern_vars s (Ast.PatLambda pl p) = foldl' pattern_vars (pattern_vars s p) pl
pattern_vars s (Ast.PatLoc _ p) = pattern_vars s p

pattern' :: Env -> Map Var SrcLoc -> SrcLoc -> Ast.Pattern -> E (Pattern, Map Var SrcLoc)
pattern' _ s _ Ast.PatAny = return (PatVar ignored, s)
pattern' _ s l (Ast.PatVar v)
  | Just l' <- Map.lookup v s = irError (show l++": duplicate definition of '"++pshow v++"', previously declared at "++show l')
  | otherwise = return (PatVar v, Map.insert v l s)
pattern' env s l (Ast.PatSpec p _) = pattern' env s l p -- XXX we don't actually do anything with these?
pattern' env s _ (Ast.PatLoc l p) = pattern' env s l p
pattern' env s l (Ast.PatOps o) = pattern' env s l (Ast.opsPattern $ sortOps (envPrecs env) o)
pattern' env s l (Ast.PatList pl) = do
  (pl, s) <- patterns' env s l pl
  return (foldr (\p pl -> PatCons (V ":") [p, pl]) (PatCons (V "[]") []) pl, s)
pattern' env s l (Ast.PatCons c pl) = first (PatCons c) =.< patterns' env s l pl
pattern' _ _ _ (Ast.PatLambda _ _) = irError "'->' (lambda) patterns not yet implemented"

patterns' :: Env -> Map Var SrcLoc -> SrcLoc -> [Ast.Pattern] -> E ([Pattern], Map Var SrcLoc)
patterns' env s l = foldM (\(pl,s) -> first (: pl) .=< pattern' env s l) ([],s) . reverse

pattern :: Env -> SrcLoc -> Ast.Pattern -> E (Pattern, Map Var SrcLoc)
pattern e l = pattern' e Map.empty l

patterns :: Env -> SrcLoc -> [Ast.Pattern] -> E ([Pattern], Map Var SrcLoc)
patterns e l = patterns' e Map.empty l

prog_precs :: Ast.Prog -> PrecEnv
prog_precs = foldl' set_precs Map.empty where
  -- TODO: error on duplicates
  set_precs s (Loc _ (Ast.Infix p vl)) = foldl' (\s v -> Map.insert v p s) s vl
  set_precs s _ = s

prog :: [Loc Ast.Decl] -> IO [Decl]
prog p = either die return (decls p) where
  env = Env $ prog_precs p
  s = prog_vars p

  -- Declaration conversion can turn multiple Ast.Decls into a single Ir.Decl, as with
  --   f :: <type>
  --   f x = ...
  -- We use Either in order to return errors.  TODO: add location information to the errors.
  decls :: [Loc Ast.Decl] -> E [Decl]
  decls [] = return []
  decls decs@(Loc _ (Ast.DefD f _ _):_) = do
    let isfcase (Loc _ (Ast.DefD (Loc _ f') a b)) | unLoc f == f' = Just (a,b)
        isfcase _ = Nothing
        (defs,rest) = spanJust isfcase decs
        s' = foldl' (foldl' pattern_vars) s (map fst defs)
    n <- case group $ map (length . fst) defs of
      [n:_] -> return n
      _ -> irError ("Equations for " ++ pshow f ++ " have different numbers of arguments")
    let (s'',vl) = freshVars s' n
    body <- cases env s'' (map Var vl) defs
    let e = foldr Lambda body vl
    (LetD f e :) =.< decls rest
  decls (Loc _ (Ast.SpecD f t) : rest) = do
    rest <- decls rest
    case rest of
      LetD f' e : rest 
        | unLoc f == unLoc f' -> return (Over f t e : rest)
        | otherwise -> irError ("Syntax error: type specification for '"++pshow f++"' followed by definition of '"++pshow f'++"'")
      _ -> irError ("Syntax error: type specification for '"++pshow f++"' must be followed by its definition")
  decls (Loc l (Ast.LetD p e) : rest)
    | Just v <- unVar p = do
      e <- expr env s e
      (LetD (Loc l v) e :) =.< decls rest
    | otherwise = do
      (p,vars) <- pattern env l p
      (_,_,m) <- match env s p Nothing
      e <- expr env s e
      let d = case map (\ (v,l) -> Loc l v) (Map.toList vars) of
                [v] -> LetD v (m e (Var (unLoc v)))
                vl -> LetM vl (m e (Cons (tupleCons vl) (map (Var . unLoc) vl)))
      (d :) =.< decls rest
  decls (Loc _ (Ast.Data t args cons) : rest) = (Data t args cons :) =.< decls rest
  decls (Loc _ (Ast.Infix _ _) : rest) = decls rest
  decls (Loc _ (Ast.Import _) : rest) = decls rest

expr :: Env -> InScopeSet -> Ast.Exp -> E Exp
expr _ _ (Ast.Int i) = return $ Int i
expr _ _ (Ast.Chr c) = return $ Chr c
expr _ _ (Ast.Var v) = return $ Var v
expr env s (Ast.Lambda pl e) = do
  (pl,_) <- patterns env noLoc pl
  (vl, s, m) <- matches env s pl Nothing
  e <- expr env s e
  return $ foldr Lambda (m (map Var vl) e) vl
expr env s (Ast.Apply f args) = do
  f <- expr env s f
  args <- mapM (expr env s) args
  return $ foldl' Apply f args
expr env s (Ast.Let p e c) = do
  e <- expr env s e
  case unVar p of
    Just v -> Let v e =.< expr env (addVar v s) c
    Nothing -> do
      (p,_) <- pattern env noLoc p
      (_,s',m) <- match env s p Nothing
      c <- expr env s' c
      return $ m e c
expr env s (Ast.Def f args body c) = do
  (args,_) <- patterns env noLoc args
  (vl, s', m) <- matches env s args Nothing
  body <- expr env s' body
  c <- expr env (Set.insert f s) c
  return $ Let f (foldr Lambda (m (map Var vl) body) vl) c
expr env s (Ast.Case e cl) = expr env s e >>= \e -> case1 env s e cl
expr env s (Ast.Ops o) = expr env s $ Ast.opsExp $ sortOps (envPrecs env) o
expr env s (Ast.Spec e t) = expr env s e >.= \e -> Spec e t
expr env s (Ast.List el) = foldr (\a b -> Cons (V ":") [a,b]) (Cons (V "[]") []) =.< mapM (expr env s) el
expr env s (Ast.If c e1 e2) = do
  c <- expr env s c
  e1 <- expr env s e1
  e2 <- expr env s e2
  return $ Apply (Apply (Apply (Var (V "if")) c) e1) e2
expr env s (Ast.ExpLoc l e) = ExpLoc l =.< expr env s e
expr _ _ Ast.Any = irError "'_' not allowed in expressions"

-- |match processes a single pattern into an input variable, a new in-scope set,
-- and a transformer that converts an input expression and a result expression
-- into new expression representing the match
match :: Env -> InScopeSet -> Pattern -> Maybe Exp -> E (Var, InScopeSet, Exp -> Exp -> Exp)
match _ s (PatVar v) _ = return (v, Set.insert v s, match_helper v)
match env s (PatCons c args) fall = do
  (vl, s', ms) <- matches env s args fall
  let (s'',x) = fresh s'
      m em er = Case em [(c, vl, ms (map Var vl) er)] (fmap ((,) ignored) fall)
  return (x, s'', m)

match_helper v em er = case em of
  Var v' | v' == v || v' == ignored -> er
  _ -> Let v em er

-- in spirit, matches = fold match
matches :: Env -> InScopeSet -> [Pattern] -> Maybe Exp -> E ([Var], InScopeSet, [Exp] -> Exp -> Exp)
matches _ s [] _ = return ([],s,\[] -> id)
matches env s (p:pl) fall = do
  (v,s,m) <- match env s p fall
  (vl,s,ml) <- matches env s pl fall
  return (v:vl, s, \ (e:el) -> m e . ml el)

type Branch = ([Pattern], Ast.Exp)
type PatTop = Either (CVar,Int) Var

-- |cases turns a multilevel pattern match into iterated single level pattern matches by
--   (1) partitioning the cases by outer element,
--   (2) performing the outer match, and
--   (3) iteratively matching the components returned in the outer match
-- Part (3) is handled by building up a stack of unprocessed expressions and an associated
-- set of pattern stacks, and then iteratively reducing the set of possibilities.
-- This generally follows Wadler's algorithm in The Implementation of Functional Programming Languages
case1 :: Env -> InScopeSet -> Exp -> [(Ast.Pattern, Ast.Exp)] -> E Exp
case1 env s e = cases env s [e] . map (first (:[]))
cases :: Env -> InScopeSet -> [Exp] -> [([Ast.Pattern], Ast.Exp)] -> E Exp
cases env s e arms = do
  (arms,vars) <- mapAndUnzipM (\(p,e) -> patterns env noLoc p >.= \(p,s) -> ((p,e),Map.keysSet s)) arms
  let vars' = Set.unions (s:vars)
  -- here we call all pattern variables "in scope" to make sure we don't end up colliding with them along the way (though see issue 22)
  reduce vars' e arms Nothing

  where 

  -- reduce takes n unmatched expressions and a list of n-tuples (lists) of patterns, and
  -- iteratively reduces the list of possibilities by matching each expression in turn.  This is
  -- used to process the stack of unmatched patterns that build up as we expand constructors.
  reduce :: InScopeSet -> [Exp] -> [Branch] -> Maybe Exp -> E Exp
  reduce s [] (([], e):_) _ = expr env s e -- no more patterns to match, so just pick the first possibility
  reduce s (val:vals) alts fall = 
    lv =.< reduceGroups s' var vals groups fall
    where
      ((s',var),lv) = case unVar val of
        Just v -> ((s,v),id)
        Nothing -> (fresh s,Let var val)
      -- separate into groups of vars vs. cons
      sameGroup (Left _, _) (Left _, _) = True
      sameGroup (Right _, _) (Right _, _) = True
      sameGroup _ _ = False
      groups = groupBy sameGroup $ map separate alts
  reduce _ _ _ _ = error "reduce: bad arguments"

  reduceGroups :: InScopeSet -> Var -> [Exp] -> [[(PatTop, Branch)]] -> Maybe Exp -> E Exp
  reduceGroups _ _ _ [] _ = error "reduceGroups: bad arguments"
  reduceGroups s var vals (group:others) fall = do
    
    next <- if null others then return fall else Just =.< reduceGroups s var vals others fall

    -- sort alternatives by toplevel tag (along with arity)
    -- note: In future, the arity might be looked up in an environment
    -- (or maybe not, if constructors are overloaded based on arity?)

    case fst $ head group of
      Left _ -> do
        let group' = groupPairs $ sortBy (on compare fst) group
        arms <- mapM (\(Left c,b) -> cons s vals (c,b) next) group'
        return $ Case (Var var) arms (fmap ((,) ignored) next)
      Right _ -> do
        let alt (Right (V "_"), pe) = pe
            alt ~(Right v, (p,e)) = (p, Ast.Let (Ast.PatVar v) (Ast.Var var) e)
            alts = map alt group
        reduce s vals alts next

  -- cons processes each case of the toplevel match
  -- If only one alternative remains, we break out of the 'reduce' recursion and switch
  -- to 'matches', which avoids trivial matches of the form "case v of v -> ..."
  cons :: InScopeSet -> [Exp] -> ((CVar,Int),[Branch]) -> Maybe Exp -> E (CVar,[Var],Exp)
  cons s vals ((c,arity),alts') fall = case alts' of
    [(pl,e)] -> do -- single alternative, use matches
      (vl,s',m) <- matches env s pl fall
      let vl' = take arity vl
          ex = (map Var vl') ++ vals
      e <- expr env s' e
      return (c,vl',m ex e)
    _ -> ex >.= (,,) c vl where -- many alernatives, use reduce
      (s',vl) = freshVars s arity
      ex = reduce s' (map Var vl ++ vals) alts' fall

  -- peel off the outer level of the first pattern, and separate into conses and defaults
  separate :: Branch -> (PatTop, Branch)
  separate ((PatVar v):l,e) = (Right v, (l,e))
  separate ((PatCons c a):l,e) = (Left (c, length a), (a++l,e))
  separate _ = error "separate: bad arguments"

instance HasVar Exp where
  var = Var
  unVar (Var v) = Just v
  unVar (ExpLoc _ e) = unVar e
  unVar (Spec e _) = unVar e
  unVar _ = Nothing

-- Pretty printing

instance Pretty Decl where
  pretty (LetD v e) =
    pretty v <+> equals <+> nest 2 (pretty e)
  pretty (LetM vl e) =
    hcat (intersperse (pretty ", ") (map pretty vl)) <+> equals <+> nest 2 (pretty e)
  pretty (Over v t e) =
    pretty v <+> pretty "::" <+> pretty t $$
    pretty v <+> equals <+> nest 2 (pretty e)
  pretty (Data t args cons) =
    pretty (Ast.Data t args cons)

instance Pretty Exp where
  pretty' (Spec e t) = (0, guard 1 e <+> pretty "::" <+> guard 60 t)
  pretty' (Let v e body) = (0,
    pretty "let" <+> pretty v <+> equals <+> guard 0 e <+> pretty "in"
      $$ guard 0 body)
  pretty' (Case e pl d) = (0,
    pretty "case" <+> pretty e <+> pretty "of" $$
    vjoin '|' (map arm pl ++ def d)) where
    arm (c, vl, e) 
      | istuple c = hcat (intersperse (pretty ", ") pvl) <+> end
      | otherwise = pretty c <+> sep pvl <+> end
      where pvl = map pretty vl
            end = pretty "->" <+> pretty e
    def Nothing = []
    def (Just (v,e)) = [pretty v <+> pretty "->" <+> pretty e]
  pretty' (Int i) = pretty' i
  pretty' (Chr c) = (100, pretty (show c))
  pretty' (Var v) = pretty' v
  pretty' (Lambda v e) = (1, pretty v <+> pretty "->" <+> nest 2 (guard 1 e))
  pretty' (Apply e1 e2) = case (apply e1 [e2]) of
    (Var v, [e1,e2]) | Just prec <- precedence v -> (prec,
      let V s = v in
      (guard prec e1) <+> pretty s <+> (guard (prec+1) e2))
    (Var c, el) | Just n <- tuplelen c, n == length el -> (1,
      hcat $ intersperse (pretty ", ") $ map (guard 2) el)
    (e, el) -> (50, guard 50 e <+> prettylist el)
    where apply (Apply e a) al = apply e (a:al) 
          apply e al = (e,al)
  pretty' (Cons (V ":") [h,t]) | Just t' <- extract t = (100,
    brackets (hcat (intersperse (pretty ", ") $ map (guard 2) (h : t')))) where
    extract (Cons (V "[]") []) = Just []
    extract (Cons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
  pretty' (Cons c args) | istuple c = (1,
    hcat $ intersperse (pretty ", ") $ map (guard 2) args)
  pretty' (Cons c args) = (50, pretty c <+> sep (map (guard 51) args))
  pretty' (Prim (Binop op) [e1,e2]) | prec <- binopPrecedence op = (prec,
    guard prec e1 <+> pretty (binopString op) <+> guard prec e2)
  pretty' (Prim prim el) = (50,
    pretty prim <+> prettylist el)
  pretty' (Bind v e1 e2) = (6,
    pretty v <+> pretty "<-" <+> guard 0 e1 $$ guard 0 e2)
  pretty' (Return e) = (6, pretty "return" <+> guard 7 e)
  pretty' (PrimIO p []) = pretty' p
  pretty' (PrimIO p args) = (50, guard 50 p <+> prettylist args)
  pretty' (ExpLoc _ e) = pretty' e
  -- pretty' (ExpLoc l e) = fmap (pretty "{-@" <+> pretty (show l) <+> pretty "-}" <+>) $ pretty' e

instance Pretty Prim where
  pretty' p = (100, pretty (show p))

instance Pretty PrimIO where
  pretty' p = (100, pretty (show p))

binopPrecedence :: Binop -> Int
binopPrecedence op = case op of
  IntAddOp -> 20
  IntSubOp -> 20
  IntMulOp -> 30
  IntDivOp -> 30
  IntEqOp -> 10
  IntLTOp -> 10
  IntLEOp -> 10
  IntGTOp -> 10
  IntGEOp -> 10

binopString :: Binop -> String
binopString op = case op of
  IntAddOp -> "+"
  IntSubOp -> "-"
  IntMulOp -> "*"
  IntDivOp -> "/"
  IntEqOp -> "=="
  IntLTOp -> "<"
  IntGTOp -> ">"
  IntLEOp -> "<="
  IntGEOp -> ">="
