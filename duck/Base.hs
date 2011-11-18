{-# LANGUAGE PatternGuards, DeriveDataTypeable #-}
-- | Duck primitive operations
--
-- This module provides the implementation for the primitive operations
-- declared in "Prims".

module Base 
  ( prim
  , primType
  , runPrimIO
  , base
  , Exception
  ) where

import Control.Monad
import qualified Control.Exception as Exn
import qualified Data.Char as Char
import Data.Functor
import Data.List
import qualified Data.Map as Map
import Data.Typeable (Typeable)

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

data Exception = Exception deriving (Show, Typeable)
instance Exn.Exception Exception

data PrimOp = PrimOp
  { primPrim :: Prim
  , primName :: String
  , primArgs :: [TypeVal]
  , primRet :: TypeVal
  , primBody :: [Value] -> IO Value
  }

intOp :: Binop -> TypeVal -> (Int -> Int -> Value) -> PrimOp
intOp op rt fun = PrimOp (Binop op) (binopString op) [typeInt, typeInt] rt $ \ ~[i,j] -> return $ fun (unsafeUnvalue i) (unsafeUnvalue j)

intBoolOp :: Binop -> (Int -> Int -> Bool) -> PrimOp
intBoolOp op fun = intOp op typeBool $ \i j -> valCons (if fun i j then 1 else 0) []

intBinOp :: Binop -> (Int -> Int -> Int) -> PrimOp
intBinOp op fun = intOp op typeInt $ \i -> value . fun i

primOps :: Map.Map Prim PrimOp
primOps = Map.fromList $ map (\o -> (primPrim o, o))
  [ intBinOp IntAddOp (+)
  , intBinOp IntSubOp (-)
  , intBinOp IntMulOp (*)
  , intBinOp IntDivOp div
  , intBoolOp IntEqOp (==)
  , intBoolOp IntLTOp (<)
  , intBoolOp IntLEOp (<=)
  , intBoolOp IntGTOp (>)
  , intBoolOp IntGEOp (>=)
  , PrimOp (Binop ChrEqOp) (binopString ChrEqOp) [typeChar, typeChar] typeBool $ \ ~[i,j] -> return $ valCons (if (unsafeUnvalue i :: Char) == unsafeUnvalue j then 1 else 0) []
  , PrimOp CharIntOrd "ord" [typeChar] typeInt $ \ ~[c] -> return $ value (Char.ord $ unsafeUnvalue c)
  , PrimOp IntCharChr "chr" [typeInt] typeChar $ \ ~[c] -> return $ value (Char.chr $ unsafeUnvalue c)
  , PrimOp Exit "exit" [typeInt] typeVoid $ \ ~[i] -> liftIO $ exit (unsafeUnvalue i :: Int)
  , PrimOp Throw "throw" [typeUnit] typeVoid $ \ _ -> Exn.throw Exception
  , PrimOp IOPutChar "put" [typeChar] typeUnit $ \ ~[c] -> valEmpty <$ liftIO (putChar (unsafeUnvalue c :: Char))
  ]

invalidPrim :: Show t => Prim -> [t] -> Doc'
invalidPrim p a = "invalid primitive arguments" <:> quoted (prettyap (V (primString p)) (map show a))

-- |Actually execute a primitive, called with the specified arguments at run time
prim :: SrcLoc -> Prim -> [Value] -> Exec Value
prim loc prim args
  | Just primop <- Map.lookup prim primOps =
    handleE (\Exception -> execError loc "uncaught exception") $
    join $ liftIO $ (Exn.catch . Exn.evaluate) (liftIO $ primBody primop args) $
      \(Exn.PatternMatchFail _) -> return $ execError loc $ invalidPrim prim args
  | otherwise = execError loc $ invalidPrim prim args

-- |Determine the type of a primitive when called with the given arguments
primType :: Bool -> SrcLoc -> Prim -> [TypeVal] -> Infer TypeVal
primType static loc prim args
  | Just primop <- Map.lookup prim primOps
  , map deStatic args == primArgs primop = do
    let rt = primRet primop
        vl = guard static >> mapM unStatic args
    maybe
      (return rt)
      (TyStatic . Any rt .=< liftIO . primBody primop) vl
  | otherwise = typeError loc $ invalidPrim prim args

-- |Execute an IO primitive
runPrimIO :: Prim -> [Value] -> Exec Value
runPrimIO Exit [i] = liftIO (exit (unsafeUnvalue i :: Int))
runPrimIO IOPutChar [c] = liftIO (putChar (unsafeUnvalue c :: Char)) >. valEmpty
runPrimIO p args = execError noLoc $ invalidPrim p args

-- |Add a undelayed, unlocated overload
overload :: Var -> [TypePat] -> TypePat -> [Var] -> Exp -> Prog -> Prog
overload name tl r args body = addOverload name $ Over noLoc tl' r args (Just body) where
  tl' = map ((,) NoTrans) tl

-- |The internal, implicit declarations giving names to primitive operations.
-- Note that this is different than base.duck.
base :: Prog
base = (complete datatypes . types . prims) (empty "") where
  primop prog p | [] <- primArgs p = prog{ progDefinitions = Def False [L noLoc name] exp : progDefinitions prog }
                | otherwise = overload name tyargs ret args exp prog where
    name = V (primName p)
    tyargs = map singleton $ primArgs p
    ret = singleton $ primRet p
    args = zipWith const standardVars $ primArgs p
    exp = ExpPrim (primPrim p) (map expLocal args)
  prims prog = foldl' primop prog $ Map.elems primOps

  types prog = prog { progDatatypes = datatypes }
  datatypes = Map.fromList $ map expand $ map (datatypeTuples !!) (0:[2..5]) ++
    [ datatypeInt, datatypeChar, datatypeDelay, datatypeType, datatypeBool ]
    where expand d = (dataName d,d)
