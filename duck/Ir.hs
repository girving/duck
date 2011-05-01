{-# LANGUAGE PatternGuards, FlexibleInstances #-}
-- | Duck Intermediate Representation
-- 
-- Conversion of "Ast" into intermediate functional representation.

module Ir 
  ( Decl(..)
  , Exp(..)
  , TypePat(..), TypeFun(..)
  , prog
  , dupError
  ) where

import Data.List
import Data.Function
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as Fold
import Data.Monoid

import Util
import Pretty
import SrcLoc
import Stage
import Var
import IrType
import Prims hiding (typeInt, typeChar)
import qualified Ast
import ParseOps

-- |Top-level declaration
data Decl
  = LetD !(Loc Var) Exp                 -- ^ Single symbol definition, either a variable or a function without a corresponding type specification (with 'Lambda'): @VAR = EXP@
  | LetM [Loc Var] Exp                  -- ^ Tuple assignment/definition, from a pattern definition with 0 or more than 1 variable: @(VARs) = EXP@
  | Over !(Loc Var) !TypePat Exp        -- ^ Overload paired type declaration and definition: @VAR :: TYPE = EXP@
  | Data !(Loc CVar) [Var] [(Loc CVar, [TypePat])] -- ^ Datatype declaration: @data CVAR VARs = { CVAR TYPEs ; ... }@
  deriving Show

-- |Expression
data Exp
  = ExpLoc SrcLoc !Exp                  -- ^ Meta source location information, present at every non-generated level
  | Int !Int
  | Char !Char
  | Var !Var
  | Lambda !Var Exp                     -- ^ Simple lambda expression: @VAR -> EXP@
  | Apply Exp Exp                       -- ^ Application: @EXP EXP@
  | Let !Var Exp Exp                    -- ^ Simple variable assignment: @let VAR = EXP in EXP@
  | Cons !CVar [Exp]                    -- ^ Constructor application: @CVAR EXPs@
  | Case Var [(CVar, [Var], Exp)] (Maybe Exp) -- ^ @case VAR of { CVAR VARs -> EXP ; ... [ ; _ -> EXP ] }@
  | Prim !Prim [Exp]                    -- ^ Primitive function call: @PRIM EXPs@
  | Spec Exp !TypePat                   -- ^ Type specification: @EXP :: TYPE@
    -- Monadic IO
  | Bind !Var Exp Exp                   -- ^ IO binding: @EXP >>= \VAR -> EXP@
  | Return Exp                          -- ^ IO return
  deriving Show

-- Ast to IR conversion

data Pattern = Pat 
  { patVars :: [Var]
  , patSpec :: [TypePat]
  , patCons :: Maybe (CVar, [Pattern])
  , patCheck :: Maybe (Var -> Exp) -- :: Bool
  }

data CaseTail
  = CaseGroup [Switch]
  | CaseBody Exp

data Case = CaseMatch
  { casePat :: [Pattern]
  , _caseLets :: Exp -> Exp
  , _caseNext :: CaseTail
  }

data Switch = Switch 
  { _switchVal :: [Exp]
  , switchCases :: [Case]
  }

irError :: Pretty s => SrcLoc -> s -> a
irError l = fatal . locMsg l

dupError :: Pretty v => v -> SrcLoc -> SrcLoc -> a
dupError v n o = irError n $ "duplicate definition of" <+> quoted v <> (", previously declared at" <&+> o)

prog_vars :: Ast.Prog -> InScopeSet
prog_vars = foldl' decl_vars Set.empty . map unLoc

decl_vars :: InScopeSet -> Ast.Decl -> InScopeSet
decl_vars s (Ast.SpecD (L _ v) _) = Set.insert v s 
decl_vars s (Ast.DefD (L _ v) _ _) = Set.insert v s 
decl_vars s (Ast.LetD p _) = pattern_vars s p
decl_vars s (Ast.Data _ _ _) = s
decl_vars s (Ast.Infix _ _) = s
decl_vars s (Ast.Import _) = s

pattern_vars :: InScopeSet -> Ast.Pattern -> InScopeSet
pattern_vars s Ast.PatAny = s
pattern_vars s (Ast.PatVar v) = Set.insert v s
pattern_vars s (Ast.PatInt _) = s
pattern_vars s (Ast.PatChar _) = s
pattern_vars s (Ast.PatCons _ pl) = foldl' pattern_vars s pl
pattern_vars s (Ast.PatOps o) = Fold.foldl' pattern_vars s o
pattern_vars s (Ast.PatList pl) = foldl' pattern_vars s pl
pattern_vars s (Ast.PatAs v p) = pattern_vars (Set.insert v s) p
pattern_vars s (Ast.PatSpec p _) = pattern_vars s p
pattern_vars s (Ast.PatLambda pl p) = foldl' pattern_vars (pattern_vars s p) pl
pattern_vars s (Ast.PatLoc _ p) = pattern_vars s p

prog_precs :: PrecEnv -> Ast.Prog -> PrecEnv
prog_precs = foldl' set_precs where
  set_precs s (L l (Ast.Infix p vl)) = foldl' (\s v -> Map.insertWithKey check v p s) s vl where
    check v new old
      | new == old = new
      | otherwise = irError l $ "conflicting fixity declaration for" <+> quoted v <+> "(previously" <+> old <+> ")"
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
anyPat = Pat [] [] Nothing Nothing

instance HasVar Pattern where
  var v = Pat [v] [] Nothing Nothing
  unVar (Pat{ patVars = v:_ }) = Just v
  unVar _ = Nothing

consPat :: CVar -> [Pattern] -> Pattern
consPat c pl = Pat [] [] (Just (c,pl)) Nothing

addPatVar :: Var -> Pattern -> Pattern
addPatVar v p = p { patVars = v : patVars p }

addPatSpec :: TypePat -> Pattern -> Pattern
addPatSpec t p = p { patSpec = t : patSpec p }

patLets :: Var -> Pattern -> Exp -> Exp
patLets var (Pat vl tl _ _) e = case (vl', tl) of
  ([],[]) -> e
  ([],_) -> Let ignored spec e
  (v:vl,_) -> letVarIf v spec $ foldr (`Let` Var var) e vl
  where 
    spec = foldl Spec (Var var) tl
    (_:vl') = nub (var:vl)

patName :: InScopeSet -> Pattern -> (InScopeSet, Var)
patName s (Pat{ patVars = v:_ }) = (s, v)
patName s (Pat{ patVars = [] }) = fresh s 

patNames :: InScopeSet -> Int -> [Pattern] -> (InScopeSet, [Var])
patNames s 0 _ = (s, [])
patNames s n [] = freshVars s n
patNames s n (p:pl) = second (v:) $ patNames s' (pred n) pl where (s',v) = patName s p 

patsNames :: InScopeSet -> Int -> [[Pattern]] -> (InScopeSet, [Var])
patsNames s n [p] = patNames s n p
patsNames s n _ = freshVars s n

mapss :: (a -> (InScopeSet, b)) -> [a] -> (InScopeSet, [b])
--mapss f = first Set.unions . unzipWith f l
mapss f = mapAccumL (\s -> first (Set.union s) . f) Set.empty

prog :: PrecEnv -> Ast.Prog -> (PrecEnv, [Decl])
prog pprec p = (precs, decls p) where
  precs = prog_precs pprec p
  globals = prog_vars p

  -- Declaration conversion can turn multiple Ast.Decls into a single Ir.Decl, as with
  --   f :: <type>
  --   f x = ...
  decls :: [Loc Ast.Decl] -> [Decl]
  decls [] = []
  decls decs@(L _ (Ast.DefD (L _ f) _ _):_) = LetD (L l f) body : decls rest where
    (L l body, rest) = funcases globals f isfcase decs
    isfcase (L l (Ast.DefD (L _ f') a b)) | f == f' = Just (L l (a,b))
    isfcase _ = Nothing
  decls (L l (Ast.SpecD (L _ f) t) : rest) = case decls rest of
    LetD (L l' f') e : rest | f == f' -> Over (L (mappend l l') f) t e : rest
    _ -> irError l $ "type specification for" <+> quoted f <+> "must be followed by its definition"
  decls (L l (Ast.LetD ap ae) : rest) = d : decls rest where
    d = case Map.toList vm of
      [] -> LetD (L l ignored) $ body $ Cons (V "()") []
      [(v,l)] -> LetD (L l v) $ body $ Var v
      vl -> LetM (map (\(v,l) -> L l v) vl) $ body $ Cons (tupleCons vl) (map (Var . fst) vl)
    body r = match globals [Switch [e] [CaseMatch [p] id (CaseBody r)]] Nothing
    e = expr globals l ae
    (p,vm) = pattern' Map.empty l ap
  decls (L _ (Ast.Data t args cons) : rest) = Data t args cons : decls rest
  decls (L _ (Ast.Infix _ _) : rest) = decls rest
  decls (L _ (Ast.Import _) : rest) = decls rest

  pattern' :: Map Var SrcLoc -> SrcLoc -> Ast.Pattern -> (Pattern, Map Var SrcLoc)
  pattern' s _ Ast.PatAny = (anyPat, s)
  pattern' s l (Ast.PatVar v)
    | Just l' <- Map.lookup v s = dupError v l l'
    | otherwise = (anyPat { patVars = [v] }, Map.insert v l s)
  pattern' s l (Ast.PatAs v p) 
    | Just l' <- Map.lookup v s = dupError v l l'
    | otherwise = first (addPatVar v) $ pattern' (Map.insert v l s) l p
  pattern' s l (Ast.PatSpec p t) = first (addPatSpec t) $ pattern' s l p
  pattern' s _ (Ast.PatLoc l p) = pattern' s l p
  pattern' s l (Ast.PatOps o) = pattern' s l (Ast.opsPattern l $ sortOps precs l o)
  pattern' s l (Ast.PatList apl) = (foldr (\p pl -> consPat (V ":") [p, pl]) (consPat (V "[]") []) pl, s') where
    (pl, s') = patterns' s l apl
  pattern' s l (Ast.PatCons c pl) = first (consPat c) $ patterns' s l pl
  pattern' s _ (Ast.PatInt i) = (anyPat { patCheck = Just (\v -> Prim (Binop IntEqOp) [Int i, Spec (Var v) typeInt]) }, s)
  pattern' s _ (Ast.PatChar c) = (anyPat { patCheck = Just (\v -> Prim (Binop ChrEqOp) [Char c, Spec (Var v) typeChar]) }, s)
  pattern' _ l (Ast.PatLambda _ _) = irError l $ quoted "->" <+> "(lambda) patterns not yet implemented"

  patterns' :: Map Var SrcLoc -> SrcLoc -> [Ast.Pattern] -> ([Pattern], Map Var SrcLoc)
  patterns' s l = foldl' (\(pl,s) -> first ((pl ++).(:[])) . pattern' s l) ([],s)

  patterns :: SrcLoc -> [Ast.Pattern] -> ([Pattern], InScopeSet)
  patterns l = fmap Map.keysSet . patterns' Map.empty l

  expr :: InScopeSet -> SrcLoc -> Ast.Exp -> Exp
  expr _ _ (Ast.Int i) = Int i
  expr _ _ (Ast.Char c) = Char c
  expr _ _ (Ast.Var v) = Var v
  expr s l (Ast.Lambda pl e) = lambdas s l pl e
  expr s l (Ast.Apply f args) = foldl' Apply (expr s l f) $ map (expr s l) args
  expr s l (Ast.Let p e c) = doMatch letpat s l (p,e,c)
  expr s l (Ast.Def f pl e ac) = Let f (lambdas s l pl e) $ expr (Set.insert f s) l ac
  expr s l (Ast.Case sl) = doMatch switches s l sl
  expr s l (Ast.Ops o) = expr s l $ Ast.opsExp l $ sortOps precs l o
  expr s l (Ast.Spec e t) = Spec (expr s l e) t
  expr s l (Ast.List el) = foldr (\a b -> Cons (V ":") [a,b]) (Cons (V "[]") []) $ map (expr s l) el
  expr s l (Ast.If c e1 e2) = Apply (Apply (Apply (Var (V "if")) $ e c) $ e e1) $ e e2 where e = expr s l
  expr s _ (Ast.Seq q) = seq s q
  expr s _ (Ast.ExpLoc l e) = ExpLoc l $ expr s l e
  expr _ l a = irError l $ quoted a <+> "not allowed in expressions"

  seq :: InScopeSet -> [Loc Ast.Stmt] -> Exp
  seq _ [] = Cons (V "()") [] -- only used when last is assignment; might as well be a warning/error
  seq s [L l (Ast.StmtExp e)] = expr s l e
  seq s (L l (Ast.StmtExp e):q) = seq s (L l (Ast.StmtLet (Ast.PatCons (V "()") []) e):q) -- should we just assign to '_'?
  seq s (L l (Ast.StmtLet p e):q) = doMatch letpat s l (p,e,Ast.Seq q)
  seq s q@(L _ (Ast.StmtDef f _ _):_) = ExpLoc l $ Let f body $ seq (Set.insert f s) rest where
    (L l body, rest) = funcases s f isfcase q -- TODO: local recursion (scope)
    isfcase (L l (Ast.StmtDef f' a b)) | f == f' = Just (L l (a,b))
    isfcase _ = Nothing

  funcases :: InScopeSet -> Var -> (a -> Maybe (Loc ([Ast.Pattern],Ast.Exp))) -> [a] -> (Loc Exp, [a])
  funcases s f isfdef dl = (L l body, rest) where
    body = lambdacases s l n (map unLoc defs)
    l = loc defs
    (defs,rest) = spanJust isfdef dl
    n = case group $ map (length . fst . unLoc) defs of
      [n:_] -> n
      _ -> irError l $ "equations for" <+> quoted f <+> "have different numbers of arguments"

  -- |process a multi-argument lambda expression
  lambdas :: InScopeSet -> SrcLoc -> [Ast.Pattern] -> Ast.Exp -> Exp
  lambdas s loc p e = lambdacases s loc (length p) [(p,e)]

  -- |process a multi-argument multi-case function set
  lambdacases :: InScopeSet -> SrcLoc -> Int -> [([Ast.Pattern], Ast.Exp)] -> Exp
  lambdacases s loc n arms = foldr Lambda body vl where
    (s',vl) = patsNames (Set.union s ps) n b
    ((ps,[b]),body) = matcher cases s' loc (vl,arms)

  letpat :: InScopeSet -> SrcLoc -> (Ast.Pattern, Ast.Exp, Ast.Exp) -> (InScopeSet, [Switch])
  letpat s0 loc (p,e,c) = (ps, [Switch [e'] [CaseMatch p' id (CaseBody c')]]) where
    (p',ps) = patterns loc [p]
    e' = expr s0 loc e
    c' = expr (Set.union s0 ps) loc c

  cases :: InScopeSet -> SrcLoc -> ([Var], [([Ast.Pattern], Ast.Exp)]) -> (InScopeSet, [Switch])
  cases s0 loc (vals,arms) = second (\b -> [Switch (map Var vals) b]) $ mapss arm arms where
    arm (p,e) = (ps,CaseMatch p' id (CaseBody e')) where
      (p',ps) = patterns loc p
      e' = expr (Set.union s0 ps) loc e

  -- Convert all the patterns and expressions in a Case Switch list (but not the switches themselves) and collect all the pattern variables.
  switches :: InScopeSet -> SrcLoc -> [Ast.Switch] -> (InScopeSet, [Switch])
  switches s0 loc = switchs Set.empty where
    switchs s = mapss (switch s)
    switch s (e,c) = second (Switch [expr s0 loc e]) $ caseline s c
    caseline s (Ast.CaseGuard r) = second ((:[]) . CaseMatch [consPat (V "True") []] id) $ casetail s r
    caseline s (Ast.CaseMatch ml) = mapss (casematch s) ml
    casematch s (p,r) = (s',CaseMatch p' id r') where 
      (p',ps) = patterns loc [p]
      (s',r') = casetail (Set.union s ps) r
    casetail s (Ast.CaseGroup l) = second CaseGroup $ switchs s l
    casetail s (Ast.CaseBody e) = (s, CaseBody $ expr (Set.union s0 s) loc e)

  doMatch :: (InScopeSet -> SrcLoc -> a -> (InScopeSet, [Switch])) -> InScopeSet -> SrcLoc -> a -> Exp
  doMatch f s l = snd . matcher f s l

  matcher :: (InScopeSet -> SrcLoc -> a -> (InScopeSet, [Switch])) -> InScopeSet -> SrcLoc -> a -> ((InScopeSet, [[[Pattern]]]), Exp)
  matcher f s l x = ((s', map (map casePat . switchCases) y), match (Set.union s s') y Nothing) where (s',y) = f s l x

  -- |match takes n unmatched expressions and a list of n-tuples (lists) of patterns, and
  -- iteratively reduces the list of possibilities by matching each expression in turn.  This is
  -- used to process the stack of unmatched patterns that build up as we expand constructors.
  --
  --   (1) partitioning the cases by outer element,
  --
  --   (2) performing the outer match, and
  --
  --   (3) iteratively matching the components returned in the outer match
  --
  -- Part (3) is handled by building up a stack of unprocessed expressions and an associated
  -- set of pattern stacks, and then iteratively reducing the set of possibilities.
  -- This generally follows Wadler's algorithm in The Implementation of Functional Programming Languages
  match :: InScopeSet -> [Switch] -> Maybe Exp -> Exp
  match = withFall switch where
    -- process a list of sequental matches
    withFall :: (InScopeSet -> a -> Maybe Exp -> Exp) -> InScopeSet -> [a] -> Maybe Exp -> Exp
    withFall _ _ [] _ = error "withFall: empty list"
    withFall f s [x] fall = f s x fall
    withFall f s (x:l) fall = letf $ f s' x (Just callf) where
      (s',fv) = freshen s (V "fall")
      letf = Let fv $ Lambda ignored $ withFall f s' l fall
      callf = Apply (Var fv) (Cons (V "()") [])

    switch :: InScopeSet -> Switch -> Maybe Exp -> Exp
    switch s (Switch [] alts) fall = withFall (\s (CaseMatch [] f e) -> f . matchTail s e) s alts fall
    switch s (Switch (val:vals) alts) fall = letVarIf var val $ withFall (matchGroup var vals) s' groups fall where
      -- separate into groups of vars vs. cons
      groups = groupBy ((==) `on` isJust . patCons . head . casePat) alts
      (s',var) = case unVar val of
        Just v -> (s,v)
        Nothing -> second head $ patsNames s 1 (map casePat alts)

    matchGroup :: Var -> [Exp] -> InScopeSet -> [Case] -> Maybe Exp -> Exp
    matchGroup var vals s group fall =
      case fst $ head alts of
        Nothing -> switch s (Switch vals (map snd alts)) fall
        Just _ -> Case var (map cons alts') fall
      where
        alts = map (\(CaseMatch (p@(Pat{ patCons = c }):pl) f e) -> (c,(CaseMatch pl (patLets var p . f) (checknext p e)))) group
        -- sort alternatives by toplevel tag (along with arity)
        alts' = groupPairs $ sortBy (on compare fst) $
              map (\(Just (c,cp), CaseMatch p pf pe) -> ((c,length cp), CaseMatch (cp++p) pf pe)) alts
        checknext (Pat{ patCheck = Just c }) e = CaseGroup [Switch [c var] [CaseMatch [consPat (V "True") []] id e]]
        checknext _ e = e
        cons ((c,arity),alts) = (c,vl, switch s' (Switch (map Var vl ++ vals) alts) fall) where
          (s',vl) = patsNames s arity (map casePat alts)

    matchTail :: InScopeSet -> CaseTail -> Maybe Exp -> Exp
    matchTail _ (CaseBody e) _ = e -- is Just fall a warning?
    matchTail s (CaseGroup l) fall = match s l fall

-- Pretty printing

instance Pretty Decl where
  pretty' (LetD v e) =
    nestedPunct '=' v e
  pretty' (LetM vl e) =
    nestedPunct '=' (punctuate ',' vl) e
  pretty' (Over v t e) =
    v <+> "::" <+> t $$
    nestedPunct '=' v e
  pretty' (Data t args cons) =
    pretty' (Ast.Data t args cons)

instance Pretty [Decl] where
  pretty' = vcat

instance Pretty Exp where
  pretty' (Spec e t) = 2 #> guard 2 e <+> "::" <+> t
  pretty' (Let v e body) = 1 #>
    "let" <+> v <+> '=' <+> pretty e <+> "in" $$ pretty body
  pretty' (Case v pl d) = 1 #>
    nested ("case" <+> v <+> "of")
      (vcat (map arm pl ++ def d)) where
    arm (c, vl, e) = prettyop c vl <+> "->" <+> pretty e
    def Nothing = []
    def (Just e) = ["_ ->" <+> pretty e]
  pretty' (Int i) = pretty' i
  pretty' (Char c) = pretty' (show c)
  pretty' (Var v) = pretty' v
  pretty' (Lambda v e) = 1 #>
    v <+> "->" <+> guard 1 e
  pretty' (Apply e1 e2) = uncurry prettyop (apply e1 [e2])
    where apply (Apply e a) al = apply e (a:al) 
          apply e al = (e,al)
  pretty' (Cons (V ":") [h,t]) | Just t' <- extract t = pretty' $
    brackets $ 3 #> punctuate ',' (h : t') where
    extract (Cons (V "[]") []) = Just []
    extract (Cons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
  pretty' (Cons c args) = prettyop c args
  pretty' (Prim p el) = prettyop (V (primString p)) el
  pretty' (Bind v e1 e2) = 0 #>
    v <+> "<-" <+> e1 $$ pretty e2
  pretty' (Return e) = prettyap "return" [e]
  pretty' (ExpLoc _ e) = pretty' e
  --pretty' (ExpLoc l e) = "{-@" <+> show l <+> "-}" <+> pretty' e
