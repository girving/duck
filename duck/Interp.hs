{-# LANGUAGE PatternGuards #-}
-- Duck interpreter

-- For now, this is dynamically typed

module Interp 
  ( prog
  , main
  ) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Data.Maybe
import Var
import Type
import Value
import Pretty
import Text.PrettyPrint
import qualified Ir
import qualified Prims
import Data.Map (Map)
import qualified Data.Map as Map
import Util
import ExecMonad
import Control.Monad hiding (guard)
import Control.Monad.Trans

-- Environments

type Overloads = Map Var [Overload]
type ConsTypes = Map Var (CVar, [Var], [Type])
data GlobalEnv = GlobalEnv
  { globalsG :: Env
  , overloadsG :: Overloads
  , consesG :: ConsTypes }

type Overload = ([Type], [Var], Ir.Exp)

emptyGlobalEnv :: GlobalEnv
emptyGlobalEnv = GlobalEnv Map.empty Map.empty Map.empty

lookup :: GlobalEnv -> Env -> Var -> Exec Value
lookup global env v
  | Just r <- Map.lookup v env = return r -- check for local definitions first
  | Just r <- Map.lookup v (globalsG global) = return r -- fall back to global definitions
  | Just _ <- Map.lookup v (overloadsG global) = return $ ValClosure v [] -- if we find overloads, make a new closure
  | otherwise = execError ("unbound variable " ++ show v)

lookupOverloads :: GlobalEnv -> Var -> [Overload]
lookupOverloads global v = Map.findWithDefault [] v (overloadsG global)

lookupConsType :: GlobalEnv -> Var -> Exec (CVar, [Var], [Type])
lookupConsType global v
  | Just r <- Map.lookup v (consesG global) = return r
  | otherwise = execError ("unbound constructor " ++ show v)

addGlobal :: GlobalEnv -> Var -> Value -> GlobalEnv
addGlobal global v d = global { globalsG = Map.insert v d (globalsG global) }

addOverload :: GlobalEnv -> Var -> Overload -> Exec GlobalEnv
addOverload global v ([],[],e) = expr global Map.empty e >>=. addGlobal global v
addOverload global v o = return $ global { overloadsG = Map.insertWith (++) v [o] (overloadsG global) }

addConsType :: GlobalEnv -> Var -> CVar -> [Var] -> [Type] -> GlobalEnv 
addConsType global v c tvl ty = global { consesG = Map.insert v (c,tvl,ty) (consesG global) }

-- Process a list of definitions into the global environment.
-- The global environment is threaded through function calls, so that
-- functions are allowed to refer to variables defined later on as long
-- as the variables are defined before the function is executed.
prog :: [Ir.Decl] -> Exec GlobalEnv
prog decls = foldM decl emptyGlobalEnv (Prims.prelude ++ decls)

-- The first environment contains all global definitions,
-- and isn't defined until after decl completes
decl :: GlobalEnv -> Ir.Decl -> Exec GlobalEnv
decl global (Ir.LetD v e) = addOverload global v (bareOverload e)
decl global (Ir.LetM vl e) = do
  d <- expr global Map.empty e
  dl <- case d of
           ValCons c dl | istuple c, length vl == length dl -> return dl
           d -> execError ("expected "++show (length vl)++"-tuple, got "++show (pretty d))
  return $ foldl (\g (v,d) -> addGlobal g v d) global (zip vl dl)
decl global (Ir.Over v t e) = addOverload global v (overload t e)
decl global (Ir.Data tc tvl cases) = return $ foldl f global cases where
  f :: GlobalEnv -> (CVar, [Type]) -> GlobalEnv
  f global (c,args) = global'' where
    global' = addGlobal global c d
    global'' = addConsType global' c tc tvl args
    d = case vl of
      [] -> ValCons c []
      _ -> ValFun Map.empty vl (Ir.Cons c (map Ir.Var vl))
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

expr :: GlobalEnv -> Env -> Ir.Exp -> Exec Value
expr global env = exp where
  exp (Ir.Int i) = return $ ValInt i
  exp (Ir.Var v) = lookup global env v
  exp (Ir.Lambda v e) = return $ ValFun env [v] e
  exp (Ir.Apply e1 e2) = do
    v1 <- exp e1
    v2 <- exp e2
    case v1 of
      ValClosure f args -> apply global f (args ++ [v2])
      ValFun env' [v] e -> expr global (Map.insert v v2 env') e
      ValFun env' (v:vl) e -> return $ ValFun (Map.insert v v2 env') vl e
      _ -> execError ("expected a -> b, got " ++ show (pretty v1))
  exp (Ir.Let v e body) = do
    d <- exp e
    expr global (Map.insert v d env) body
  exp (Ir.Case e pl def) = do
    d <- exp e
    case d of
      ValCons c dl -> case find (\ (c',_,_) -> c == c') pl of
        Just (_,vl,e') ->
          if a == length dl then
            expr global (foldl (\s (v,d) -> Map.insert v d s) env (zip vl dl)) e'
          else
            execError ("arity mismatch in pattern: "++show (pretty c)++" expected "++show a++" argument"++(if a == 1 then "" else "s")
              ++" but got ["++concat (intersperse "," (map (show . pretty) vl))++"]")
          where a = length vl
        Nothing -> case def of
          Nothing -> execError ("pattern match failed: exp = " ++ show (pretty d) ++ ", cases = " ++ show pl)
          Just (v,e') -> expr global (Map.insert v d env) e' 
      _ -> execError ("expected block, got " ++ show (pretty d))
  exp (Ir.Cons c el) = ValCons c =<<. mapM exp el
  exp (Ir.Binop op e1 e2) = do
    d1 <- exp e1
    d2 <- exp e2
    Prims.prim op d1 d2
  exp (Ir.Bind v e1 e2) = do
    d <- exp e1
    return (ValBindIO v d e2)
  exp (Ir.Return e) = exp e >>=. ValLiftIO
  exp (Ir.PrimIO p el) = mapM exp el >>=. ValPrimIO p

-- Overloaded function application
apply :: GlobalEnv -> Var -> [Value] -> Exec Value
apply global f args = do
  types <- mapM (typeof global) args
  let call = unwords (map show (pretty f : map (guard 51) types))
      prune o@(tl,_,_) = case unifyList tl types of
        Just _ -> Just o
        Nothing -> Nothing
      overloads = catMaybes (map prune rawOverloads) -- prune those that don't match
      isSpecOf a b = isJust (unifyList b a)
      isMinimal (tl,_,_) = all (\ (tl',_,_) -> isSpecOf tl tl' || not (isSpecOf tl' tl)) overloads
      rawOverloads = lookupOverloads global f -- look up possibilities
      options overs = concatMap (\ (tl,_,_) -> concat ("\n  " : intersperse " -> " (map (show . guard 2) tl)) ++ " -> ...") overs
  case filter isMinimal overloads of -- prune away overloads which are more general than some other overload
    [] -> execError (call++" doesn't match any overload, possibilities are"++options rawOverloads)
    os -> case partition (\ (_,l,_) -> length l == length args) os of
      ([],_) -> return $ ValClosure f args -- all overloads are still partially applied
      ([(_,vl,e)],[]) -> withFrame f args $ -- exactly one fully applied option
        expr global (foldl (\env (v,d) -> Map.insert v d env) Map.empty (zip vl args)) e
      (fully@(_:_),partially@(_:_)) -> execError (call++" is ambiguous, could either be fully applied as"++options fully++"\nor partially applied as"++options partially)
      (fully@(_:_:_),[]) -> execError (call++" is ambiguous, possibilities are"++options fully)

typeof :: GlobalEnv -> Value -> Exec Type
typeof _ (ValInt _) = return TyInt
typeof global (ValCons c args) = do
  tl <- mapM (typeof global) args
  (tv, vl, tl') <- lookupConsType global c
  case unifyList tl' tl of
    Just tenv -> return $ TyApply tv targs where
      targs = map (\v -> Map.findWithDefault TyVoid v tenv) vl
    Nothing -> execError ("failed to unify types "++showlist tl++" with "++showlist tl') where
      showlist = unwords . (map (show . guard 51))
typeof _ (ValFun _ _ _) = return $ TyFun TyVoid TyVoid
typeof _ (ValClosure _ _) = return $ TyFun TyVoid TyVoid
typeof _ (ValBindIO _ _ _) = return $ TyIO TyVoid
typeof _ (ValPrimIO _ _) = return $ TyIO TyVoid
typeof _ (ValLiftIO _) = return $ TyIO TyVoid

-- IO and main
main :: GlobalEnv -> IO ()
main global = runExec $ do
  main <- lookup global Map.empty (V "main")
  _ <- runIO global Map.empty main
  return ()

runIO :: GlobalEnv -> Env -> Value -> Exec Value
runIO _ _ (ValLiftIO d) = return d
runIO global _ (ValPrimIO Ir.TestAll []) = testAll global
runIO _ _ (ValPrimIO p args) = Prims.primIO p args
runIO global env (ValBindIO v m e) = do
  d <- runIO global env m
  let env' = Map.insert v d env
  d' <- expr global env' e
  runIO global env' d'
runIO _ _ d =
  execError ("expected IO computation, got "++show (pretty d))

testAll :: GlobalEnv -> Exec Value
testAll global = do
  liftIO $ putStrLn "running unit tests..."
  mapM_ test (Map.toList (globalsG global))
  liftIO $ putStrLn "success!"
  nop
  where
  test (V v,d)
    | isPrefixOf "test_" v = do
        liftIO $ putStrLn ("  "++v)
        runIO global Map.empty d
    | otherwise = nop
  nop = return $ ValCons (V "()") []

-- Pretty printing

instance Pretty GlobalEnv where
  pretty (GlobalEnv global overs _) = Map.foldWithKey overloads (pretty global) overs where
    overloads v os s = foldl (overload v) s os
    overload :: Var -> Doc -> Overload -> Doc
    overload v s (tl, vl, e) = s $$ text "" $$
      text "over" <+> hsep (intersperse (text "->") (map (guard 2) tl)) <+> text "-> ..." $$
      text "let" <+> pretty v <+> hsep (map pretty vl) <+> equals <+> pretty e
