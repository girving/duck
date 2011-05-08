{-# LANGUAGE ScopedTypeVariables #-}
-- | Duck interpreter

module Main where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.List
import Control.Monad 
import System.Environment
import System.FilePath
import System.Directory
import System.Console.GetOpt
import System.IO
import System.Exit
import Control.Exception

import Util
import Var
import Stage
import Pretty
import Parse
import ParseMonad
import qualified Ast
import qualified Ir
import qualified Lir
import qualified ToLir
import qualified Interp
import qualified Base
import qualified Infer
import ExecMonad
import InferMonad
import ToHaskell

-- Options

data Flags = Flags
  { phases :: Set Stage
  , compileOnly :: Bool
  , toHaskell :: Bool
  , path :: [FilePath]
  }
type Option = OptDescr (Flags -> IO Flags)

enumOption :: Enum e => [String] -> [Char] -> [String] -> String -> (e -> Flags -> Flags) -> String -> Option
enumOption choices short long name f help = Option short long (ReqArg process name) help' where
  help' = help ++ " (one of " ++ intercalate "," choices ++ ")"
  process p x = case findIndices (isPrefixOf p) choices of
    [e] -> return $ f (toEnum e) x
    [] -> die 1 $ "Unknown " ++ name ++ ". Choices are: " ++ intercalate "," choices
    l -> die 1 $ "Ambiguous " ++ name ++ ". Choices are: " ++ intercalate "," (map (choices !!) l)

options :: [Option]
options =
  [ enumOption stageNames ['d'] ["dump"] "PHASE" (\p f -> f { phases = Set.insert p (phases f) }) "dump internal data"
  , Option ['c'] [] (NoArg $ \f -> return $ f { compileOnly = True }) "compile only, don't evaluate main"
  , Option [] ["haskell"] (NoArg $ \f -> return $ f { toHaskell = True }) "generate equivalent Haskell code from AST"
  , Option ['I'] ["include"] (ReqArg (\p f -> return $ f { path = path f ++ [p] }) "DIRECTORY") "add DIRECTORY to module search path"
  , Option ['h'] ["help"] (NoArg $ \_ -> putStr usage >> exitSuccess) "show this help" ]
usage = usageInfo "duck [options] [files...]" options

defaults = Flags
  { phases = Set.empty
  , compileOnly = False
  , toHaskell = False
  , path = [""]
  }

findModule :: [FilePath] -> ModuleName -> MaybeT IO FilePath
findModule l s = do
  let ext = ".duck"
      f | takeExtension s == ext = s
        | otherwise = addExtension s (tail ext)
  msum $ map (MaybeT . (\p -> doesFileExist p >.= \e -> Control.Monad.guard e >. p) . (</> f)) l

loadModule :: Set ModuleName -> [FilePath] -> ModuleName -> IO [(ModuleName, Ast.Prog)]
loadModule s l m = do
  (f,c) <- case m of
    "" -> ((,) "<stdin>") =.< getContents
    m -> runMaybeT (findModule l m) >>= maybe 
      (fatalIO $ msg ("module" <+> quoted m <+> "not found"))
      (\f -> ((,) (dropExtension f)) =.< readFile f)
  let (d,f') = splitFileName f
      l' = l `union` [d]
      s' = Set.insert f' s
      imp v
        | Set.member v s' = return []
        | otherwise = loadModule s' l' v
      ast = runP parse f' c
  asts <- mapM imp $ Ast.imports ast
  return $ concat asts ++ [(f',ast)]

main = do
  (options, args, errors) <- getOpt Permute options =.< getArgs
  case errors of
    [] -> return ()
    _ -> fputs stderr (concat errors ++ usage) >> exitFailure
  flags <- foldM (\t s -> s t) defaults options

  f <- case args of
    [] -> puts "Duck interactive mode" >. ""
    [file] -> return file
    _ -> fail "expected zero or one arguments"

  let ifv p = when (Set.member p (phases flags))
  let phase p pf io = do
        ifv p $ putStr ("\n-- "++show (pretty p)++" --\n")
        r <- runStage p io
        ifv p $ pout $ pf r
        return r
      phase' p pf = phase p pf . evaluate

  (names,ast) <- phase StageParse (concat . snd) (unzip =.< loadModule Set.empty (path flags) f)
  when (toHaskell flags) $ (pout $ uncurry ToHaskell.prog $ head $ reverse $ zip names ast :: IO ()) >> exitSuccess

  ir <- phase' StageIr concat (snd $ mapAccumL Ir.prog Map.empty ast)
  lir <- phase' StageLir id (ToLir.progs Base.base (zip names ir))
  runStage StageLink $ evaluate $ Lir.check lir
  lir <- phase StageInfer id (runInferProg Infer.prog lir)

  unless (compileOnly flags) $ do
  _ <- phase StageExec (\v -> (Lir.progGlobalTypes lir, v)) (runExec lir Interp.prog)
  return ()

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
