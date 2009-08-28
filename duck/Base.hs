{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operations
--
-- This module provides the implementation for the primitive operations
-- declared in "Prims".

module Base 
  ( prim
  , primType
  , primIO
  , primIOType
  , base
  ) where

import Control.Monad
import Control.Monad.Trans (liftIO)
import qualified Control.Exception as Exn
import qualified Data.Char as Char
import qualified Data.Map as Map

import Util
import Var
import Type
import Value
import Prims
import SrcLoc
import Pretty
import Ir
import qualified Lir
import ExecMonad
import InferMonad

data PrimOp = PrimOp
  { primPrim :: Prim
  , primName :: String
  , primArgs :: [Type]
  , primRet :: Type
  , primBody :: [Value] -> Value
  }

intOp :: Binop -> Type -> (Int -> Int -> Value) -> PrimOp
intOp op rt fun = PrimOp (Binop op) (binopString op) [tyInt, tyInt] rt $ \[ValInt i, ValInt j] -> fun i j

intBoolOp :: Binop -> (Int -> Int -> Bool) -> PrimOp
intBoolOp op fun = intOp op (TyCons (V "Bool") []) $ \i j -> ValCons (V $ if fun i j then "True" else "False") []

intBinOp :: Binop -> (Int -> Int -> Int) -> PrimOp
intBinOp op fun = intOp op tyInt $ \i -> ValInt . fun i

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
  , PrimOp ChrIntOrd "ord" [tyChr] tyInt $ \[ValChr c] -> ValInt (Char.ord c)
  , PrimOp IntChrChr "chr" [tyInt] tyChr $ \[ValInt c] -> ValChr (Char.chr c)
  ]

-- |Actually execute a primitive, called with the specified arguments at run time
prim :: SrcLoc -> Prim -> [Value] -> Exec Value
prim loc prim args
  | Just primop <- Map.lookup prim primOps = do
    join $ liftIO $ (Exn.catch . Exn.evaluate) (return $ (primBody primop) args) $
      \(Exn.PatternMatchFail _) -> return $ execError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)
  | otherwise = execError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)

-- |Determine the type of a primitive when called with the given arguments
primType :: SrcLoc -> Prim -> [Type] -> Infer Type
primType loc prim args
  | Just primop <- Map.lookup prim primOps
  , args == primArgs primop = return $ primRet primop
  | otherwise = typeError loc ("invalid primitive application: " ++ show prim ++ " " ++ pshow args)

-- |Equivalent to 'prim' for IO primitives
primIO :: PrimIO -> [Value] -> Exec Value
primIO Exit [ValInt i] = liftIO (exit i)
primIO IOPutChr [ValChr c] = liftIO (putChar c) >. valUnit
primIO p args = execError noLoc ("invalid arguments "++pshowlist args++" to "++show p)

-- |Equivalent to 'primType' for IO primitives
primIOType :: SrcLoc -> PrimIO -> [Type] -> Infer Type
primIOType _ Exit [i] | isTyInt i = return TyVoid
primIOType _ IOPutChr [c] | isTyChr c = return tyUnit
primIOType _ TestAll [] = return tyUnit
primIOType loc p args = typeError loc ("invalid arguments"++pshowlist args++" to "++show p)

-- |The internal, implicit declarations giving names to primitive operations.
-- Note that this is different than base.duck.
base :: Lir.Prog
base = Lir.union types (Lir.prog (decTuples ++ prims ++ io)) where
  primop p = Ir.Over
      (Loc noLoc $ V (primName p)) 
      (foldr tsArrow (singleton $ primRet p) (map singleton $ primArgs p))
      (foldr Lambda (Prim (primPrim p) (map Var args)) args)
    where args = zipWith const standardVars $ primArgs p
  prims = map primop $ Map.elems primOps

  decTuples = map decTuple [2..5]
  decTuple i = Data c vars [(c, map TsVar vars)] where
    c = Loc noLoc $ tupleCons vars
    vars = take i standardVars

  types = Lir.empty { Lir.progVariances = Map.fromList
    [ (V "Int", [])
    , (V "Chr", [])
    , (V "IO", [Covariant]) 
    , (V "Delayed", [Covariant])
    , (V "Type", [Invariant])
    ] }

io :: [Decl]
io = [map',join,exit,ioPutChr,testAll,returnIO] where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TsVar [a,b]
  map' = Over (Loc noLoc $ V "map") (tsArrow (tsArrow ta tb) (tsArrow (tsIO ta) (tsIO tb)))
    (Lambda f (Lambda c
      (Bind x (Var c)
      (Return (Apply (Var f) (Var x))))))
  join = Over (Loc noLoc $ V "join") (tsArrow (tsIO (tsIO ta)) (tsIO ta))
    (Lambda c
      (Bind x (Var c)
      (Var x)))
  returnIO = LetD (Loc noLoc $ V "returnIO") (Lambda x (Return (Var x)))
  exit = Over (Loc noLoc $ V "exit") (tsArrow tsInt (tsIO TsVoid)) (Lambda x (PrimIO Exit [Var x]))
  ioPutChr = Over (Loc noLoc $ V "put") (tsArrow tsChr (tsIO tsUnit)) (Lambda c (PrimIO IOPutChr [Var c]))
  testAll = LetD (Loc noLoc $ V "testAll") (PrimIO TestAll [])
