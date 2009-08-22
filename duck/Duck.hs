{-# LANGUAGE ScopedTypeVariables #-}
-- | Duck interpreter

module Main where

import Parse
import ParseMonad
import Pretty
import System.Environment
import System.FilePath
import System.Directory
import System.Console.GetOpt
import System.IO
import System.Exit
import qualified Ast
import qualified Ir
import qualified Lir
import qualified Interp
import qualified Base
import qualified Infer
import ExecMonad
import InferMonad
import Control.Monad 
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.List
import Util
import Stage

-- Options

data Flags = Flags
  { phases :: Set Stage
  , compileOnly :: Bool
  , path :: [FilePath]
  }
type Option = OptDescr (Flags -> IO Flags)

enumOption :: forall e . (Read e, Show e, Enum e, Bounded e) => [Char] -> [String] -> String -> (e -> Flags -> Flags) -> String -> Option
enumOption short long name f help = Option short long (ReqArg process name) help' where
  help' = help ++ " (one of " ++ intercalate "," (map show (allOf :: [e])) ++ ")"
  process p = return . f (read p)

options :: [Option]
options =
  [ enumOption ['d'] ["dump"] "PHASE" (\p f -> f { phases = Set.insert p (phases f) }) "dump internal data"
  , Option ['c'] [] (NoArg $ \f -> return $ f { compileOnly = True }) "compile only, don't evaluate main"
  , Option ['I'] ["include"] (ReqArg (\p f -> return $ f { path = p : path f }) "DIRECTORY") "add DIRECTORY to module search path"
  , Option ['h'] ["help"] (NoArg $ \_ -> putStr usage >> exitSuccess) "show this help" ]
usage = usageInfo "duck [options] [files...]" options

defaults = Flags
  { phases = Set.empty
  , compileOnly = False
  , path = [""]
  }

type ModuleName = String

findModule :: [FilePath] -> ModuleName -> MaybeT IO FilePath
findModule l s = do
  let ext = ".duck"
      f | takeExtension s == ext = s
        | otherwise = addExtension s (tail ext)
  msum $ map (MaybeT . (\p -> doesFileExist p >.= returnIf p) . (</> f)) l

loadModule :: Set ModuleName -> [FilePath] -> ModuleName -> IO Ast.Prog
loadModule s l m = do
  (f,c) <- case m of
    "" -> ((,) "<stdin>") =.< getContents
    m -> runMaybeT (findModule l m) >>= maybe 
      (fail ("module '" ++ pshow m ++ "' not found"))
      (\f -> ((,) (dropExtension f)) =.< readFile f)
  let l' = l `union` [takeDirectory f]
      s' = Set.insert m s
      imp v
        | Set.member v s' = return []
        | otherwise = loadModule s' l' v
  ast <- runP parse f c
  asts <- mapM imp $ Ast.imports ast
  return $ concat asts ++ ast

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
  let phase p io = do
        ifv p $ putStr ("\n-- "++pshow p++" --\n")
        r <- catchFatal io
        ifv p $ pprint r
        return r
      phase' p = phase p . return

  ast <- phase StageParse (loadModule Set.empty (path flags) f)
  ir <- phase StageIr (Ir.prog ast)
  lir <- phase' StageLir (Lir.prog ir)
  lir <- phase' StageLink (Lir.union Base.base lir)
  Lir.check lir
  lir <- phase StageInfer (liftM fst $ runInfer [] Map.empty $ Infer.prog lir)
  unless (compileOnly flags) $ rerunInfer [] lir (Infer.main lir)
  env <- phase StageEnv (runExec $ Interp.prog lir)

  unless (compileOnly flags) $ do
    unless (Set.null (phases flags)) $ putStr "\n-- Main --\n"
    Interp.main lir env

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
