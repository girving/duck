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

binop :: SrcLoc -> Binop -> Value -> Value -> Exec Value
binop _ IntAddOp (ValInt i) (ValInt j) = return $ ValInt (i+j)
binop _ IntSubOp (ValInt i) (ValInt j) = return $ ValInt (i-j)
binop _ IntMulOp (ValInt i) (ValInt j) = return $ ValInt (i*j)
binop _ IntDivOp (ValInt i) (ValInt j) = return $ ValInt (div i j)
binop _ IntEqOp (ValInt i) (ValInt j) = return $ ValCons (V (if i == j then "True" else "False")) []
binop _ IntLessOp (ValInt i) (ValInt j) = return $ ValCons (V (if i < j then "True" else "False")) []
binop loc op v1 v2 = execError loc ("invalid arguments "++(pshow v1)++", "++(pshow v2)++" to "++show op)

prim :: SrcLoc -> Prim -> [Value] -> Exec Value
prim loc (Binop op) [v1,v2] = binop loc op v1 v2
prim loc op vl = execError loc ("invailid primitive application: " ++ show op ++ " " ++ (pshow vl))

binopType :: SrcLoc -> Binop -> Type -> Type -> Infer Type
binopType _ IntAddOp TyInt TyInt = return TyInt
binopType _ IntSubOp TyInt TyInt = return TyInt
binopType _ IntMulOp TyInt TyInt = return TyInt
binopType _ IntDivOp TyInt TyInt = return TyInt
binopType _ IntEqOp TyInt TyInt = return $ TyCons (V "Bool") []
binopType _ IntLessOp TyInt TyInt = return $ TyCons (V "Bool") []
binopType loc op t1 t2 = typeError loc ("invalid arguments "++(pshow t1)++", "++(pshow t2)++" to "++show op)

primType :: SrcLoc -> Prim -> [Type] -> Infer Type
primType loc (Binop op) [t1,t2] = binopType loc op t1 t2
primType loc op t = typeError loc ("invalid primitive application: " ++ show op ++ " " ++ (pshow t))

primIO :: PrimIO -> [Value] -> Exec Value
primIO ExitFailure [] = execError noLoc "exit failure"
primIO p args = execError noLoc ("invalid arguments "++show (prettylist args)++" to "++show p)

primIOType :: SrcLoc -> PrimIO -> [Type] -> Infer Type
primIOType _ ExitFailure [] = return tyUnit
primIOType _ TestAll [] = return tyUnit
primIOType loc p args = typeError loc ("invalid arguments"++show (prettylist args)++" to "++show p)

prelude :: IO Lir.Prog
prelude = Lir.prog $ decTuples ++ prims ++ io where
  [a,b] = take 2 standardVars
  ty = TsFun TsInt (TsFun TsInt (TsVar a))
  binops = map binop [IntAddOp, IntSubOp, IntMulOp, IntDivOp, IntEqOp, IntLessOp]
  binop op = Ir.Over (Loc noLoc $ V (binopString op)) ty (Lambda a (Lambda b (Prim (Binop op) [Var a, Var b])))
  prims = binops

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
