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

primType :: Binop -> Type -> Type -> Infer Type
primType IntAddOp TyInt TyInt = return TyInt
primType IntSubOp TyInt TyInt = return TyInt
primType IntMulOp TyInt TyInt = return TyInt
primType IntDivOp TyInt TyInt = return TyInt
primType IntEqOp TyInt TyInt = return $ TyCons (V "Bool") []
primType IntLessOp TyInt TyInt = return $ TyCons (V "Bool") []
primType op t1 t2 = typeError ("invalid arguments "++show (pretty t1)++", "++show (pretty t2)++" to "++show op)

primIO :: PrimIO -> [Value] -> Exec Value
primIO ExitFailure [] = execError noLoc "exit failure"
primIO p args = execError noLoc ("invalid arguments "++show (prettylist args)++" to "++show p)

primIOType :: PrimIO -> [Type] -> Infer Type
primIOType ExitFailure [] = return $ TyCons (V "()") []
primIOType TestAll [] = return $ TyCons (V "()") []
primIOType p args = typeError ("invalid arguments"++show (prettylist args)++" to "++show p)

prelude :: Lir.Prog
prelude = Lir.prog $ decTuples ++ binops ++ io where
  [a,b] = take 2 standardVars
  ty = TsFun TsInt (TsFun TsInt (TsVar a))
  binops = map binop [IntAddOp, IntSubOp, IntMulOp, IntDivOp, IntEqOp, IntLessOp]
  binop op = Ir.Over (V (binopString op)) ty (Lambda a (Lambda b (Binop op (Var a) (Var b))))

  decTuples = map decTuple [2..5]
  decTuple i = Data c vars [(c, map TsVar vars)] where
    c = tuple vars
    vars = take i standardVars

io :: [Decl]
io = [map',join,exitFailure,testAll,returnIO] where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TsVar [a,b]
  map' = Over (V "map") (TsFun (TsFun ta tb) (TsFun (TsIO ta) (TsIO tb)))
    (Lambda f (Lambda c
      (Bind x (Var c)
      (Return (Apply (Var f) (Var x))))))
  join = Over (V "join") (TsFun (TsIO (TsIO ta)) (TsIO ta))
    (Lambda c
      (Bind x (Var c)
      (Var x)))
  returnIO = LetD (V "returnIO") (Lambda x (Return (Var x)))
  exitFailure = LetD (V "exitFailure") (PrimIO ExitFailure [])
  testAll = LetD (V "testAll") (PrimIO TestAll [])
