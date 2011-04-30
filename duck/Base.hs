{-# LANGUAGE PatternGuards #-}
-- | Duck primitive operations
--
-- This module provides the implementation for the primitive operations
-- declared in "Prims".

module Base 
  ( prim
  , primType
  , runPrimIO
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
import Memory
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
  , primArgs :: [TypeVal]
  , primRet :: TypeVal
  , primBody :: [Value] -> Value
  }

intOp :: Binop -> TypeVal -> (Int -> Int -> Value) -> PrimOp
intOp op rt fun = PrimOp (Binop op) (binopString op) [typeInt, typeInt] rt $ \[i,j] -> fun (unsafeUnvalue i) (unsafeUnvalue j)

intBoolOp :: Binop -> (Int -> Int -> Bool) -> PrimOp
intBoolOp op fun = intOp op (TyCons (V "Bool") []) $ \i j -> valCons (if fun i j then 1 else 0) []

intBinOp :: Binop -> (Int -> Int -> Int) -> PrimOp
intBinOp op fun = intOp op typeInt $ \i -> value . fun i

ioOp :: Prim -> String -> [TypeVal] -> TypeVal -> PrimOp
ioOp p name tl t = PrimOp p name tl (typeIO t) (value . ValPrimIO p)

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
  , PrimOp (Binop ChrEqOp) (binopString ChrEqOp) [typeChar, typeChar] (TyCons (V "Bool") []) $ \[i,j] -> valCons (if (unsafeUnvalue i :: Char) == unsafeUnvalue j then 1 else 0) []
  , PrimOp CharIntOrd "ord" [typeChar] typeInt $ \[c] -> value (Char.ord $ unsafeUnvalue c)
  , PrimOp IntCharChr "chr" [typeInt] typeChar $ \[c] -> value (Char.chr $ unsafeUnvalue c)
  , ioOp Exit "exit" [typeInt] typeVoid
  , ioOp IOPutChar "put" [typeChar] typeUnit
  , ioOp TestAll "testAll" [] typeUnit
  ]

invalidPrim :: Show t => Prim -> [t] -> Doc'
invalidPrim p a = "invalid primitive arguments" <:> quoted (prettyap (V (primString p)) (map show a))

-- |Actually execute a primitive, called with the specified arguments at run time
prim :: SrcLoc -> Prim -> [Value] -> Exec Value
prim loc prim args
  | Just primop <- Map.lookup prim primOps = do
    join $ liftIO $ (Exn.catch . Exn.evaluate) (return $ (primBody primop) args) $
      \(Exn.PatternMatchFail _) -> return $ execError loc $ invalidPrim prim args
  | otherwise = execError loc $ invalidPrim prim args

-- |Determine the type of a primitive when called with the given arguments
primType :: SrcLoc -> Prim -> [TypeVal] -> Infer TypeVal
primType loc prim args
  | Just primop <- Map.lookup prim primOps
  , args == primArgs primop = return $ primRet primop
  | otherwise = typeError loc $ invalidPrim prim args

-- |Execute an IO primitive
runPrimIO :: Prim -> [Value] -> Exec Value
runPrimIO Exit [i] = liftIO (exit (unsafeUnvalue i :: Int))
runPrimIO IOPutChar [c] = liftIO (putChar (unsafeUnvalue c :: Char)) >. valEmpty
runPrimIO p args = execError noLoc $ invalidPrim p args

-- |The internal, implicit declarations giving names to primitive operations.
-- Note that this is different than base.duck.
base :: Lir.Prog
base = Lir.union types (Lir.prog "" (decTuples ++ prims ++ io)) where
  primop p | [] <- primArgs p = Ir.LetD name exp
           | otherwise = Ir.Over name sig exp where
    name = L noLoc $ V (primName p)
    sig = foldr typeArrow (singleton $ primRet p) (map singleton $ primArgs p)
    args = zipWith const standardVars $ primArgs p
    exp = foldr Lambda (Prim (primPrim p) (map Var args)) args
  prims = map primop $ Map.elems primOps

  decTuples = map decTuple (0:[2..5])
  decTuple i = Ir.Data c vars [(c, map TsVar vars)] where
    c = L noLoc $ tupleCons vars
    vars = take i standardVars

  types = (Lir.empty "")
    { Lir.progDatatypes = Map.fromList $ map expand
      [ Lir.Data (V "Int") noLoc [] [] []
      , Lir.Data (V "Char") noLoc [] [] []
      , Lir.Data (V "IO") noLoc [V "a"] [] [Covariant]
      , Lir.Data (V "Delayed") noLoc [V "a"] [] [Covariant]
      , Lir.Data (V "Type") noLoc [V "t"] [] [Invariant]
      ]
    }
    where expand d@(Lir.Data t _ _ _ _) = (t,d)

io :: [Decl]
io = [map',join,returnIO] where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TsVar [a,b]
  map' = Over (L noLoc $ V "map") (typeArrow (typeArrow ta tb) (typeArrow (typeIO ta) (typeIO tb)))
    (Lambda f (Lambda c
      (Bind x (Var c)
      (Return (Apply (Var f) (Var x))))))
  join = Over (L noLoc $ V "join") (typeArrow (typeIO (typeIO ta)) (typeIO ta))
    (Lambda c
      (Bind x (Var c)
      (Var x)))
  returnIO = LetD (L noLoc $ V "returnIO") (Lambda x (Return (Var x)))
