{-# LANGUAGE PatternGuards #-}
-- | Duck Intermediate Representation

module Ir 
  ( Decl(..)
  , Exp(..)
  , prog
  , binopString
  ) where

import Data.List
import Data.Function
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as Fold
import Control.Monad hiding (guard)
import GHC.Exts
import Util
import Pretty
import SrcLoc
import Stage
import Var
import Type
import Prims
import qualified Ast
import ParseOps

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
  | Case Var [(CVar, [Var], Exp)] (Maybe Exp)
  | Prim !Prim [Exp]
  | Spec Exp !TypeSet
    -- Monadic IO
  | Bind !Var Exp Exp
  | Return Exp
  | PrimIO !PrimIO [Exp]
  deriving Show

-- Ast to IR conversion

data Pattern = Pat 
  { patVars :: [Var]
  , patSpec :: [TypeSet]
  , patCons :: Maybe (CVar, [Pattern])
  } deriving (Show)

type Branch = ([Pattern], Exp)

irError :: SrcLoc -> String -> a
irError = stageError StageIr

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
pattern_vars s (Ast.PatAs v p) = pattern_vars (Set.insert v s) p
pattern_vars s (Ast.PatSpec p _) = pattern_vars s p
pattern_vars s (Ast.PatLambda pl p) = foldl' pattern_vars (pattern_vars s p) pl
pattern_vars s (Ast.PatLoc _ p) = pattern_vars s p

prog_precs :: Ast.Prog -> PrecEnv
prog_precs = foldl' set_precs Map.empty where
  set_precs s (Loc l (Ast.Infix p vl)) = foldl' (\s v -> Map.insertWithKey check v p s) s vl where
    check v new old
      | new == old = new
      | otherwise = irError l $ "conflicting fixity declaration for " ++ qshow v ++ " (previously " ++ pshow old ++ ")"
  set_precs s _ = s

instance HasVar Exp where
  var = Var
  unVar (Var v) = Just v
  unVar (ExpLoc _ e) = unVar e
  unVar _ = Nothing

letVarIf :: Var -> Exp -> Exp -> Exp
letVarIf var val exp
  | Just v <- unVar val
  , v == var = exp
  | otherwise = Let var val exp

anyPat :: Pattern
anyPat = Pat [] [] Nothing

instance HasVar Pattern where
  var v = Pat [v] [] Nothing
  unVar (Pat (v:_) _ _) = Just v
  unVar _ = Nothing

consPat :: CVar -> [Pattern] -> Pattern
consPat c pl = Pat [] [] (Just (c,pl))

addPatVar :: Var -> Pattern -> Pattern
addPatVar v p = p { patVars = v : patVars p }

addPatSpec :: TypeSet -> Pattern -> Pattern
addPatSpec t p = p { patSpec = t : patSpec p }

patLets :: Var -> Pattern -> Exp -> Exp
patLets var (Pat vl tl _) e = case (vl', tl) of
  ([],[]) -> e
  ([],_) -> Let ignored spec e
  (v:vl,_) -> letVarIf v spec $ foldr (`Let` Var var) e vl
  where 
    spec = foldl Spec (Var var) tl
    (_:vl') = nub (var:vl)

patName :: InScopeSet -> Pattern -> (InScopeSet, Var)
patName s (Pat (v:_) _ _) = (s, v)
patName s (Pat [] _ _) = fresh s 

patNames :: InScopeSet -> Int -> [Pattern] -> (InScopeSet, [Var])
patNames s 0 _ = (s, [])
patNames s n [] = freshVars s n
patNames s n (p:pl) = second (v:) $ patNames s' (pred n) pl where (s',v) = patName s p 

matchNames :: InScopeSet -> Int -> [Branch] -> (InScopeSet, [Var])
matchNames s n [(p,_)] = patNames s n p
matchNames s n _ = freshVars s n

prog :: [Loc Ast.Decl] -> [Decl]
prog p = decls p where
  precs = prog_precs p
  globals = prog_vars p

  -- Declaration conversion can turn multiple Ast.Decls into a single Ir.Decl, as with
  --   f :: <type>
  --   f x = ...
  decls :: [Loc Ast.Decl] -> [Decl]
  decls [] = []
  decls decs@(Loc loc (Ast.DefD f _ _):_) = LetD f body : decls rest where
    body = lambdacases (Set.insert (unLoc f) globals) loc n defs
    (defs,rest) = spanJust isfcase decs
    isfcase (Loc _ (Ast.DefD (Loc _ f') a b)) | unLoc f == f' = Just (a,b)
    isfcase _ = Nothing
    n = case group $ map (length . fst) defs of
      [n:_] -> n
      _ -> irError loc $ "equations for " ++ qshow f ++ " have different numbers of arguments"
  decls (Loc loc (Ast.SpecD f t) : rest) = case decls rest of
    LetD (Loc _ f') e : rest | unLoc f == f' -> Over f t e : rest
    _ -> irError loc $ "type specification for "++qshow f++" must be followed by its definition"
  decls (Loc l (Ast.LetD ap ae) : rest) = d : decls rest where
    d = case Map.toList vm of
      [(v,l)] -> LetD (Loc l v) $ body $ Var v
      vl -> LetM (map (\(v,l) -> Loc l v) vl) $ body $ Cons (tupleCons vl) (map (Var . fst) vl)
    body r = match (Set.union globals $ Map.keysSet vm) [e] [([p],r)] Nothing
    e = expr globals l ae
    (p,vm) = pattern' Map.empty l ap
  decls (Loc _ (Ast.Data t args cons) : rest) = Data t args cons : decls rest
  decls (Loc _ (Ast.Infix _ _) : rest) = decls rest
  decls (Loc _ (Ast.Import _) : rest) = decls rest

  pattern' :: Map Var SrcLoc -> SrcLoc -> Ast.Pattern -> (Pattern, Map Var SrcLoc)
  pattern' s _ Ast.PatAny = (anyPat, s)
  pattern' s l (Ast.PatVar v)
    | Just l' <- Map.lookup v s = irError l $ "duplicate definition of "++qshow v++"; previously declared at "++show l'
    | otherwise = (anyPat { patVars = [v] }, Map.insert v l s)
  pattern' s l (Ast.PatAs v p) = first (addPatVar v) $ pattern' s l p
  pattern' s l (Ast.PatSpec p t) = first (addPatSpec t) $ pattern' s l p
  pattern' s _ (Ast.PatLoc l p) = pattern' s l p
  pattern' s l (Ast.PatOps o) = pattern' s l (Ast.opsPattern l $ sortOps precs l o)
  pattern' s l (Ast.PatList apl) = (foldr (\p pl -> consPat (V ":") [p, pl]) (consPat (V "[]") []) pl, s') where
    (pl, s') = patterns' s l apl
  pattern' s l (Ast.PatCons c pl) = first (consPat c) $ patterns' s l pl
  pattern' _ l (Ast.PatLambda _ _) = irError l $ qshow "->" ++ " (lambda) patterns not yet implemented"

  patterns' :: Map Var SrcLoc -> SrcLoc -> [Ast.Pattern] -> ([Pattern], Map Var SrcLoc)
  patterns' s l = foldl' (\(pl,s) -> first ((pl ++).(:[])) . pattern' s l) ([],s)

  patterns :: SrcLoc -> [Ast.Pattern] -> ([Pattern], InScopeSet)
  patterns l = fmap Map.keysSet . patterns' Map.empty l

  expr :: InScopeSet -> SrcLoc -> Ast.Exp -> Exp
  expr _ _ (Ast.Int i) = Int i
  expr _ _ (Ast.Chr c) = Chr c
  expr _ _ (Ast.Var v) = Var v
  expr s l (Ast.Lambda pl e) = lambdas s l pl e
  expr s l (Ast.Apply f args) = foldl' Apply (expr s l f) $ map (expr s l) args
  expr s l (Ast.Let p e c) = case1 s l (expr s l e) [(p,c)]
  expr s l (Ast.Def f pl e ac) = Let f (lambdas s l pl e) $ expr (Set.insert f s) l ac
  expr s l (Ast.Case e cl) = case1 s l (expr s l e) cl
  expr s l (Ast.Ops o) = expr s l $ Ast.opsExp l $ sortOps precs l o
  expr s l (Ast.Spec e t) = Spec (expr s l e) t
  expr s l (Ast.List el) = foldr (\a b -> Cons (V ":") [a,b]) (Cons (V "[]") []) $ map (expr s l) el
  expr s l (Ast.If c e1 e2) = Apply (Apply (Apply (Var (V "if")) $ e c) $ e e1) $ e e2 where e = expr s l
  expr s _ (Ast.ExpLoc l e) = ExpLoc l $ expr s l e
  expr _ l a = irError l $ qshow a ++ " not allowed in expressions"

  -- |process a multi-argument lambda expression
  lambdas :: InScopeSet -> SrcLoc -> [Ast.Pattern] -> Ast.Exp -> Exp
  lambdas s loc p e = lambdacases s loc (length p) [(p,e)]

  -- |process a multi-argument multi-case function set
  lambdacases :: InScopeSet -> SrcLoc -> Int -> [([Ast.Pattern], Ast.Exp)] -> Exp
  lambdacases s loc n arms = foldr Lambda body vl where
    (s',vl) = matchNames (Set.union s ps) n b
    ((ps,b),body) = cases s' loc (map Var vl) arms

  -- |process a single-argument case expression
  case1 :: InScopeSet -> SrcLoc -> Exp -> [(Ast.Pattern, Ast.Exp)] -> Exp
  case1 s loc v = snd . cases s loc [v] . map (first (:[]))

  -- |cases turns a multilevel pattern match into iterated single level pattern matches by
  --   (1) partitioning the cases by outer element,
  --   (2) performing the outer match, and
  --   (3) iteratively matching the components returned in the outer match
  -- Part (3) is handled by building up a stack of unprocessed expressions and an associated
  -- set of pattern stacks, and then iteratively reducing the set of possibilities.
  -- This generally follows Wadler's algorithm in The Implementation of Functional Programming Languages
  cases :: InScopeSet -> SrcLoc -> [Exp] -> [([Ast.Pattern], Ast.Exp)] -> ((InScopeSet, [Branch]), Exp)
  cases ss loc vals aarms = (sa, match (Set.union ss s') vals arms Nothing) where 
    sa@(s',arms) = mapAccumL (\s -> first (Set.union s) . arm) Set.empty aarms
    arm (ap,ae) = (ps,(p,e)) where
      (p,ps) = patterns loc ap
      e = expr (Set.union ss ps) loc ae

  -- match takes n unmatched expressions and a list of n-tuples (lists) of patterns, and
  -- iteratively reduces the list of possibilities by matching each expression in turn.  This is
  -- used to process the stack of unmatched patterns that build up as we expand constructors.
  match :: InScopeSet -> [Exp] -> [Branch] -> Maybe Exp -> Exp
  match _ [] (([], e):_) _ = e -- no more patterns to match, so just pick the first possibility
  match ss ~(val:vals) alts fall = letVarIf var val $ matchGroups s groups fall where
    -- separate into groups of vars vs. cons
    groups = groupBy ((==) `on` isJust . patCons . head . fst) alts
    (s,var) = case unVar val of
      Just v -> (ss,v)
      Nothing -> second head $ matchNames ss 1 alts

    matchGroups :: InScopeSet -> [[Branch]] -> Maybe Exp -> Exp
    matchGroups s [group] fall = matchGroup s group fall
    matchGroups s ~(group:others) fall = letf $ matchGroup s' group $ Just callf where
      -- this should become a (local) function to avoid code duplication
      (s',fv) = freshen s (V "fall")
      letf = Let fv $ Lambda ignored $ matchGroups s' others fall
      callf = Apply (Var fv) (Cons (V "()") [])

    matchGroup :: InScopeSet -> [Branch] -> Maybe Exp -> Exp
    matchGroup s [(p@(Pat _ _ c):pats,exp)] fall =
      patLets var p $ case c of
        Nothing -> match s vals [(pats,exp)] fall
        Just (c,cp) -> Case var [cons s (c,length cp) [(cp++pats,exp)] fall] fall
    matchGroup s group fall =
      case fst $ head alts of
        Nothing -> match s vals (map snd alts) fall
        Just _ -> Case var (map (\(c,b) -> cons s c b fall) alts') fall
      where
        alts = map (\(p@(Pat _ _ c):pl,e) -> (c,(pl,patLets var p e))) group
        -- sort alternatives by toplevel tag (along with arity)
        alts' = groupPairs $ sortBy (on compare fst) $
              map (\(Just (c,cp),(p,e)) -> ((c,length cp), (cp++p,e))) alts

    -- cons processes each case of the toplevel match
    cons :: InScopeSet -> (CVar,Int) -> [Branch] -> Maybe Exp -> (CVar,[Var],Exp)
    cons s (c,arity) alts fall = (c,vl, match s' (map Var vl ++ vals) alts fall) where
      (s',vl) = matchNames s arity alts

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
  pretty' (Case v pl d) = (0,
    pretty "case" <+> pretty v <+> pretty "of" $$
    vjoin '|' (map arm pl ++ def d)) where
    arm (c, vl, e) 
      | istuple c = hcat (intersperse (pretty ", ") pvl) <+> end
      | otherwise = pretty c <+> sep pvl <+> end
      where pvl = map pretty vl
            end = pretty "->" <+> pretty e
    def Nothing = []
    def (Just e) = [pretty "_" <+> pretty "->" <+> pretty e]
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
  --pretty' (ExpLoc l e) = fmap (pretty "{-@" <+> pretty (show l) <+> pretty "-}" <+>) $ pretty' e
