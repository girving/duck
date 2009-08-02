{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operations

module Prims 
  ( prim
  , primType
  , prelude
  , primIO
  , primIOType
  ) where

import Var
import Type
import Value
import SrcLoc
import Pretty
import Ir
import qualified Lir
import ExecMonad
import InferMonad

prim :: SrcLoc -> Binop -> Value -> Value -> Exec Value
prim _ IntAddOp (ValInt i) (ValInt j) = return $ ValInt (i+j)
prim _ IntSubOp (ValInt i) (ValInt j) = return $ ValInt (i-j)
prim _ IntMulOp (ValInt i) (ValInt j) = return $ ValInt (i*j)
prim _ IntDivOp (ValInt i) (ValInt j) = return $ ValInt (div i j)
prim _ IntEqOp (ValInt i) (ValInt j) = return $ ValCons (V (if i == j then "True" else "False")) []
prim _ IntLessOp (ValInt i) (ValInt j) = return $ ValCons (V (if i < j then "True" else "False")) []
prim loc op v1 v2 = execError loc ("invalid arguments "++show (pretty v1)++", "++show (pretty v2)++" to "++show op)

primType :: SrcLoc -> Binop -> Type -> Type -> Infer Type
primType _ IntAddOp TyInt TyInt = return TyInt
primType _ IntSubOp TyInt TyInt = return TyInt
primType _ IntMulOp TyInt TyInt = return TyInt
primType _ IntDivOp TyInt TyInt = return TyInt
primType _ IntEqOp TyInt TyInt = return $ TyCons (V "Bool") []
primType _ IntLessOp TyInt TyInt = return $ TyCons (V "Bool") []
primType loc op t1 t2 = typeError loc ("invalid arguments "++show (pretty t1)++", "++show (pretty t2)++" to "++show op)

primIO :: PrimIO -> [Value] -> Exec Value
primIO ExitFailure [] = execError noLoc "exit failure"
primIO p args = execError noLoc ("invalid arguments "++show (prettylist args)++" to "++show p)

primIOType :: SrcLoc -> PrimIO -> [Type] -> Infer Type
primIOType _ ExitFailure [] = return $ TyCons (V "()") []
primIOType _ TestAll [] = return $ TyCons (V "()") []
primIOType loc p args = typeError loc ("invalid arguments"++show (prettylist args)++" to "++show p)

prelude :: IO Lir.Prog
prelude = Lir.prog $ decTuples ++ binops ++ io where
  [a,b] = take 2 standardVars
  ty = TsFun TsInt (TsFun TsInt (TsVar a))
  binops = map binop [IntAddOp, IntSubOp, IntMulOp, IntDivOp, IntEqOp, IntLessOp]
  binop op = Ir.Over (Loc noLoc $ V (binopString op)) ty (Lambda a (Lambda b (Binop op (Var a) (Var b))))

  decTuples = map decTuple [2..5]
  decTuple i = Data c vars [(c, map TsVar vars)] where
    c = Loc noLoc $ tupleCons vars
    vars = take i standardVars

io :: [Decl]
io = [map',join,exitFailure,testAll,returnIO] where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TsVar [a,b]
  map' = Over (Loc noLoc $ V "map") (TsFun (TsFun ta tb) (TsFun (TsIO ta) (TsIO tb)))
    (Lambda f (Lambda c
      (Bind x (Var c)
      (Return (Apply (Var f) (Var x))))))
  join = Over (Loc noLoc $ V "join") (TsFun (TsIO (TsIO ta)) (TsIO ta))
    (Lambda c
      (Bind x (Var c)
      (Var x)))
  returnIO = LetD (Loc noLoc $ V "returnIO") (Lambda x (Return (Var x)))
  exitFailure = LetD (Loc noLoc $ V "exitFailure") (PrimIO ExitFailure [])
  testAll = LetD (Loc noLoc $ V "testAll") (PrimIO TestAll [])
