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
import Data.List

import Util
import Var
import Type
import Memory
import Value
import Prims
import SrcLoc
import Pretty
import Lir
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
intOp op rt fun = PrimOp (Binop op) (binopString op) [typeInt, typeInt] rt $ \ ~[i,j] -> fun (unsafeUnvalue i) (unsafeUnvalue j)

intBoolOp :: Binop -> (Int -> Int -> Bool) -> PrimOp
intBoolOp op fun = intOp op typeBool $ \i j -> valCons (if fun i j then 1 else 0) []

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
  , PrimOp (Binop ChrEqOp) (binopString ChrEqOp) [typeChar, typeChar] typeBool $ \ ~[i,j] -> valCons (if (unsafeUnvalue i :: Char) == unsafeUnvalue j then 1 else 0) []
  , PrimOp CharIntOrd "ord" [typeChar] typeInt $ \ ~[c] -> value (Char.ord $ unsafeUnvalue c)
  , PrimOp IntCharChr "chr" [typeInt] typeChar $ \ ~[c] -> value (Char.chr $ unsafeUnvalue c)
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

-- |Add a undelayed, unlocated overload
overload :: Prog -> Var -> [TypePat] -> TypePat -> [Var] -> Exp -> Prog
overload prog name tl r args body = prog{ progFunctions = Map.insertWith (++) name [over] $ progFunctions prog } where
  over = Over noLoc tl' r args (Just body)
  tl' = map ((,) NoTrans) tl

-- |The internal, implicit declarations giving names to primitive operations.
-- Note that this is different than base.duck.
base :: Prog
base = (complete datatypes . types . prims . io) (empty "") where
  primop prog p | [] <- primArgs p = prog{ progDefinitions = Def [L noLoc name] exp : progDefinitions prog }
                | otherwise = overload prog name tyargs ret args exp where
    name = V (primName p)
    tyargs = map singleton $ primArgs p
    ret = singleton $ primRet p
    args = zipWith const standardVars $ primArgs p
    exp = ExpPrim (primPrim p) (map expLocal args)
  prims prog = foldl' primop prog $ Map.elems primOps

  types prog = prog { progDatatypes = datatypes }
  datatypes = Map.fromList $ map expand $ map ((!!) datatypeTuples) (0:[2..5]) ++
    [ datatypeInt, datatypeChar, datatypeIO, datatypeDelay, datatypeType, datatypeBool ]
    where expand d = (dataName d,d)

io :: Prog -> Prog
io prog = map' $ join $ returnIO prog where
  [f,a,b,c,x] = map V ["f","a","b","c","x"]
  [ta,tb] = map TsVar [a,b]
  map' p = overload p (V "map") [typeArrow ta tb, typeIO ta] (typeIO tb) [f,c] $
    (ExpBind x (expLocal c)
    (ExpReturn (ExpApply (expLocal f) (expLocal x))))
  join p = overload p (V "join") [typeIO (typeIO ta)] (typeIO ta) [c]
    (ExpBind x (expLocal c)
    (expLocal x))
  returnIO p = overload p (V "returnIO") [TsVar a] (typeIO (TsVar a)) [x]
    (ExpReturn (expLocal x))
