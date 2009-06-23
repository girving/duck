{-# LANGUAGE PatternGuards #-}
-- Duck primitive operations

module Prims 
  ( prim
  , prelude
  , primIO
  ) where

import Var
import Type
import Value
import Pretty
import Ir
import ExecMonad
import Text.PrettyPrint

prim :: Binop -> Value -> Value -> Exec Value
prim IntAddOp (ValInt i) (ValInt j) = return $ ValInt (i+j)
prim IntSubOp (ValInt i) (ValInt j) = return $ ValInt (i-j)
prim IntMulOp (ValInt i) (ValInt j) = return $ ValInt (i*j)
prim IntDivOp (ValInt i) (ValInt j) = return $ ValInt (div i j)
prim IntEqOp (ValInt i) (ValInt j) = return $ ValCons (V (if i == j then "True" else "False")) []
prim IntLessOp (ValInt i) (ValInt j) = return $ ValCons (V (if i < j then "True" else "False")) []
prim op v1 v2 = execError ("invalid arguments "++show (pretty v1)++", "++show (pretty v2)++" to "++show op)

primIO :: PrimIO -> [Value] -> Exec Value
primIO ExitFailure [] = execError "exit failure"
primIO p args = execError ("invalid arguments "++show (hsep (map pretty args))++" to "++show p)

prelude :: [Decl]
prelude = decTuples ++ binops ++ io where
  [a,b] = take 2 standardVars
  ty = TyFun TyInt (TyFun TyInt (TyVar a))
  binops = map binop [IntAddOp, IntSubOp, IntMulOp, IntDivOp, IntEqOp, IntLessOp]
  binop op = Over (V (binopString op)) ty (Lambda a (Lambda b (Binop op (Var a) (Var b))))

  decTuples = map decTuple (0 : [2..5])
  decTuple i = Data c vars [(c, map TyVar vars)] where
    c = tuple vars
    vars = take i standardVars

io :: [Decl]
io = [map',join,exitFailure,testAll,returnIO] where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TyVar [a,b]
  map' = Over (V "map") (TyFun (TyFun ta tb) (TyFun (TyIO ta) (TyIO tb)))
    (Lambda f (Lambda c
      (Bind x (Var c)
      (Return (Apply (Var f) (Var x))))))
  join = Over (V "join") (TyFun (TyIO (TyIO ta)) (TyIO ta))
    (Lambda c
      (Bind x (Var c)
      (Var x)))
  returnIO = LetD (V "returnIO") (Lambda x (Return (Var x)))
  exitFailure = LetD (V "exitFailure") (PrimIO ExitFailure [])
  testAll = LetD (V "testAll") (PrimIO TestAll [])
