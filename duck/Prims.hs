{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operations

module Prims 
  ( prim
  , primType
  , prelude
  , primIO
  , primIOType
  ) where

import Util
import Var
import Type
import Value
import SrcLoc
import Pretty
import Ir
import qualified Lir
import ExecMonad
import InferMonad
import Control.Monad
import Control.Monad.Trans (liftIO)
import qualified Control.Exception as Exn
import qualified Data.Char as Char
import qualified Data.Map as Map


data PrimOp = PrimOp
  { primPrim :: Prim
  , primName :: String
  , primArgs :: [Type]
  , primRet :: Type
  , primBody :: [Value] -> Value
  }

intOp :: Binop -> Type -> (Int -> Int -> Value) -> PrimOp
intOp op rt fun = PrimOp (Binop op) (binopString op) [TyInt, TyInt] rt $ \[ValInt i, ValInt j] -> fun i j

intBoolOp :: Binop -> (Int -> Int -> Bool) -> PrimOp
intBoolOp op fun = intOp op (TyCons (V "Bool") []) $ \i j -> ValCons (V $ if fun i j then "True" else "False") []

intBinOp :: Binop -> (Int -> Int -> Int) -> PrimOp
intBinOp op fun = intOp op TyInt $ \i -> ValInt . fun i

primOps :: Map.Map Prim PrimOp
primOps = Map.fromList $ map (\o -> (primPrim o, o)) $
  [ intBinOp IntAddOp (+)
  , intBinOp IntSubOp (-)
  , intBinOp IntMulOp (*)
  , intBinOp IntDivOp div
  , intBoolOp IntEqOp (==)
  , intBoolOp IntLTOp (<)
  , intBoolOp IntLEOp (<=)
  , intBoolOp IntGTOp (>)
  , intBoolOp IntGEOp (>=)
  , PrimOp ChrIntOrd "ord" [TyChr] TyInt $ \[ValChr c] -> ValInt (Char.ord c)
  , PrimOp IntChrChr "chr" [TyInt] TyChr $ \[ValInt c] -> ValChr (Char.chr c)
  ]

prim :: SrcLoc -> Prim -> [Value] -> Exec Value
prim loc prim args
  | Just primop <- Map.lookup prim primOps = do
    join $ liftIO $ (Exn.catch . Exn.evaluate) (return $ (primBody primop) args) $
      \(Exn.PatternMatchFail _) -> return $ execError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)
  | otherwise = execError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)

primType :: SrcLoc -> Prim -> [Type] -> Infer Type
primType loc prim args
  | Just primop <- Map.lookup prim primOps
  , args == primArgs primop = return $ primRet primop
  | otherwise = typeError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)

primIO :: PrimIO -> [Value] -> Exec Value
primIO ExitFailure [] = execError noLoc "exit failure"
primIO IOPutChr [ValChr c] = liftIO (putChar c) >. valUnit
primIO p args = execError noLoc ("invalid arguments "++show (prettylist args)++" to "++show p)

primIOType :: SrcLoc -> PrimIO -> [Type] -> Infer Type
primIOType _ ExitFailure [] = return tyUnit
primIOType _ IOPutChr [TyChr] = return tyUnit
primIOType _ TestAll [] = return tyUnit
primIOType loc p args = typeError loc ("invalid arguments"++show (prettylist args)++" to "++show p)

prelude :: IO Lir.Prog
prelude = Lir.prog $ decTuples ++ prims ++ io where
  primop p = Ir.Over 
      (Loc noLoc $ V (primName p)) 
      (foldr TsFun (singleton $ primRet p) (map singleton $ primArgs p))
      (foldr Lambda (Prim (primPrim p) (map Var args)) args)
    where args = zipWith const standardVars $ primArgs p
  prims = map primop $ Map.elems primOps

  decTuples = map decTuple [2..5]
  decTuple i = Data c vars [(c, map TsVar vars)] where
    c = Loc noLoc $ tupleCons vars
    vars = take i standardVars

io :: [Decl]
io = [map',join,exitFailure,ioPutChr,testAll,returnIO] where
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
  ioPutChr = Over (Loc noLoc $ V "put") (TsFun TsChr (TsIO (singleton tyUnit))) (Lambda c (PrimIO IOPutChr [Var c]))
  testAll = LetD (Loc noLoc $ V "testAll") (PrimIO TestAll [])
