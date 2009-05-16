-- Duck interpreter

-- For now, this is dynamically typed

module Interp where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Data.Maybe
import Var
import Type
import Pretty
import Text.PrettyPrint
import qualified Ir
import Data.Map (Map)
import qualified Data.Map as Map
import Util()

-- Environments

type Env = Map Var Value
type Overloads = Map Var [Overload]
type ConsTypes = Map Var (CVar, [Var], [Type])
data GlobalEnv = GlobalEnv
  { globalsG :: Env
  , overloadsG :: Overloads
  , consesG :: ConsTypes }

data Value
  = ValInt Int
  | ValCons Var [Value]
  | ValFun Env Var Ir.Exp
  | ValClosure Var [Value]

type Overload = ([Type], [Var], Ir.Exp)

emptyGlobalEnv :: GlobalEnv
emptyGlobalEnv = GlobalEnv Map.empty Map.empty Map.empty

lookup :: GlobalEnv -> Env -> Var -> Value
lookup global env v
  | Just r <- Map.lookup v env = r -- check for local definitions first
  | Just r <- Map.lookup v (globalsG global) = r -- fall back to global definitions
  | Just _ <- Map.lookup v (overloadsG global) = ValClosure v [] -- if we find overloads, make a new closure
  | otherwise = error ("unbound variable " ++ show v)

lookupOverloads :: GlobalEnv -> Var -> [Overload]
lookupOverloads global v = Map.findWithDefault [] v (overloadsG global)

lookupConsType :: GlobalEnv -> Var -> (CVar, [Var], [Type])
lookupConsType global v
  | Just r <- Map.lookup v (consesG global) = r
  | otherwise = error ("unbound constructor " ++ show v)

addGlobal :: GlobalEnv -> Var -> Value -> GlobalEnv
addGlobal global v d = global { globalsG = Map.insert v d (globalsG global) }

addOverload :: GlobalEnv -> Var -> Overload -> GlobalEnv
addOverload global v ([],[],e) = addGlobal global v (expr global Map.empty e)
addOverload global v o = global { overloadsG = Map.insertWith (++) v [o] (overloadsG global) }

addConsType :: GlobalEnv -> Var -> CVar -> [Var] -> [Type] -> GlobalEnv 
addConsType global v c tvl ty = global { consesG = Map.insert v (c,tvl,ty) (consesG global) }

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: [Ir.Decl] -> GlobalEnv
prog decls = foldl decl emptyGlobalEnv (prelude ++ decls)

-- The first environment contains all global definitions,
-- and isn't defined until after decl completes
decl :: GlobalEnv -> Ir.Decl -> GlobalEnv
decl global (Ir.LetD v e) = addOverload global v (bareOverload e)
decl global (Ir.LetMD vl e) = foldl (\g (v,d) -> addGlobal g v d) global (zip vl dl) where
  dl = case expr global Map.empty e of
    ValCons c dl | istuple c, length vl == length dl -> dl
    d -> error ("expected "++show (length vl)++"-tuple, got "++show (pretty d))
decl global (Ir.OverD v t e) = addOverload global v (overload t e)
decl global (Ir.Data tc tvl cases) = foldl f global cases where
  f :: GlobalEnv -> (CVar, [Type]) -> GlobalEnv
  f global (c,args) = global'' where
    global' = addGlobal global c (expr global Map.empty ir)
    global'' = addConsType global' c tc tvl args
    ir = foldr Ir.Lambda (Ir.Cons c (map Ir.Var vl)) vl
    vl = take (length args) standardVars

-- Unwrap a type/lambda combination as far as we can
overload :: Type -> Ir.Exp -> Overload
overload (TyFun t tl) (Ir.Lambda v e) = (t:tl', v:vl, e') where
  (tl', vl, e') = overload tl e
overload _ e = ([], [], e)

-- Unwrap a lambda as far as we can
bareOverload :: Ir.Exp -> Overload
bareOverload e = (tl, vl, e') where
  helper (Ir.Lambda v e) = (v:vl, e') where
    (vl, e') = helper e
  helper e = ([], e)
  (vl, e') = helper e
  tl = map TyVar (take (length vl) standardVars)

expr :: GlobalEnv -> Env -> Ir.Exp -> Value
expr global env = exp where
  exp (Ir.Int i) = ValInt i
  exp (Ir.Var v) = lookup global env v
  exp (Ir.Lambda v e) = ValFun env v e
  exp (Ir.Apply e1 e2) = case v1 of
    ValClosure f args -> apply global f (args ++ [v2])
    ValFun env' v e -> expr global (Map.insert v v2 env') e
    _ -> error ("expected a -> b, got " ++ show (pretty v1))
    where v1 = exp e1
          v2 = exp e2
  exp (Ir.Let v e body) = expr global (Map.insert v (exp e) env) body
  exp (Ir.Case e pl def) = case d of
    ValCons c dl -> case find (\ (c',_,_) -> c == c') pl of
      Just (_,vl,e') -> expr global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl dl)) e'
      Nothing -> case def of
        Nothing -> error ("pattern match failed: exp = " ++ show (pretty d) ++ ", cases = " ++ show pl)
        Just (v,e') -> expr global (Map.insert v d env) e' 
    _ -> error ("expected block, got " ++ show (pretty d))
    where d = exp e
  exp (Ir.Cons c el) = ValCons c (map exp el)
  exp (Ir.Binop op e1 e2) = prim op (exp e1) (exp e2)

-- Overloaded function application
apply :: GlobalEnv -> Var -> [Value] -> Value
apply global f args = result where
  result = case filter isMinimal overloads of -- prune away overloads which are more general than some other overload
    [] -> error (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition (\ (_,l,_) -> length l == length args) os of
      ([],_) -> ValClosure f args -- all overloads are still partially applied
      ([(_,vl,e)],[]) -> expr global (foldl (\env (v,d) -> Map.insert v d env) Map.empty (zip vl args)) e -- exactly one fully applied option
      (fully@(_:_),partially@(_:_)) -> error (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)
      (fully@(_:_:_),[]) -> error (call++" is ambiguous, possibilities are"++options fully)
  types = map (typeof global) args
  rawOverloads = lookupOverloads global f -- look up possibilities
  overloads = catMaybes (map prune rawOverloads) -- prune those that don't match
  call = unwords (map show (pretty f : map (guard 51) types))
  options overs = concatMap (\ (tl,_,_) -> concat ("\n  " : intersperse " -> " (map (show . guard 2) tl)) ++ " -> ...") overs
  prune o@(tl,_,_) = case unifyList tl types of
    Just _ -> Just o
    Nothing -> Nothing
  isSpecOf a b = isJust (unifyList b a)
  isMinimal (tl,_,_) = all (\ (tl',_,_) -> isSpecOf tl tl' || not (isSpecOf tl' tl)) overloads

typeof :: GlobalEnv -> Value -> Type
typeof _ (ValInt _) = TyInt
typeof global (ValCons c args) = TyApply tv targs where
  tl = map (typeof global) args
  (tv, vl, tl') = lookupConsType global c
  tenv = case unifyList tl' tl of
    Just tenv -> tenv
    Nothing -> error ("failed to unify types "++showlist tl++" with "++showlist tl') where
      showlist = unwords . (map (show . guard 51))
  targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
typeof _ (ValFun _ _ _) = TyFun TyVoid TyVoid
typeof _ (ValClosure _ _) = TyFun TyVoid TyVoid

prim :: Ir.Binop -> Value -> Value -> Value
prim Ir.IntAddOp (ValInt i) (ValInt j) = ValInt (i+j)
prim Ir.IntSubOp (ValInt i) (ValInt j) = ValInt (i-j)
prim Ir.IntMulOp (ValInt i) (ValInt j) = ValInt (i*j)
prim Ir.IntDivOp (ValInt i) (ValInt j) = ValInt (div i j)
prim op v1 v2 = error ("invalid arguments "++show (pretty v1)++", "++show (pretty v2)++" to "++show op)

prelude :: [Ir.Decl]
prelude = decTuples ++ binops where
  [a,b] = take 2 standardVars
  ty = TyFun TyInt (TyFun TyInt TyInt)
  binops = map binop [Ir.IntAddOp, Ir.IntSubOp, Ir.IntMulOp, Ir.IntDivOp ]
  binop op = Ir.OverD (V (Ir.binopString op)) ty (Ir.Lambda a (Ir.Lambda b (Ir.Binop op (Ir.Var a) (Ir.Var b))))

  decTuples = map decTuple (0 : [2..5])
  decTuple i = Ir.Data c vars [(c, map TyVar vars)] where
    c = tuple vars
    vars = take i standardVars

-- Pretty printing

instance Pretty Value where
  pretty' (ValInt i) = pretty' i
  pretty' (ValCons c []) = pretty' c
  pretty' (ValCons c fields) | istuple c = (1,
    hcat $ intersperse (text ", ") $ map (guard 2) fields)
  pretty' (ValCons c fields) = (2, pretty c <+> sep (map (guard 3) fields))
  pretty' (ValFun _ v e) = -- conveniently ignore env
    (0, text "\\" <> pretty v <> text " -> " <> pretty e)
  pretty' (ValClosure v args) = (2, pretty v <+> sep (map (guard 3) args))

instance Pretty GlobalEnv where
  pretty (GlobalEnv global overs _) = Map.foldWithKey overloads (pretty global) overs where
    overloads v os s = foldl (overload v) s os
    overload :: Var -> Doc -> Overload -> Doc
    overload v s (tl, vl, e) = s $$ text "" $$
      text "over" <+> hsep (intersperse (text "->") (map (guard 2) tl)) <+> text "-> ..." $$
      text "let" <+> pretty v <+> hsep (map pretty vl) <+> equals <+> pretty e
