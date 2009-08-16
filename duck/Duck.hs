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
import qualified Prims
import qualified Infer
import ExecMonad
import InferMonad
import Control.Monad
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.List
import Util

-- Options

data Phase = PAst | PIr | PLir | PLink | PInfer | PEnv
  deriving (Enum, Bounded, Ord, Eq)

instance Pretty Phase where
  pretty = pretty . f where
    f PAst = "ast"
    f PIr = "ir"
    f PLir = "lir"
    f PLink = "link"
    f PInfer = "infer"
    f PEnv = "env"

data Flags = Flags
  { phases :: Set Phase
  , compileOnly :: Bool
  , path :: [FilePath]
  }
type Option = OptDescr (Flags -> IO Flags)

enumOption :: (Pretty e, Enum e, Bounded e) => [Char] -> [String] -> String -> e -> (e -> Flags -> Flags) -> String -> Option
enumOption short long name x f help = Option short long (ReqArg process name) help' where
  help' = help ++ " (one of " ++ concat (intersperse ", " (map pshow values)) ++ ")"
  values = enumFrom (minBound `asTypeOf` x)
  process :: String -> Flags -> IO Flags
  process s flags = case lookup s [(pshow x,x) | x <- values] of
    Nothing -> die ("invalid argument "++s++" to --"++head long)
    Just x -> return (f x flags)

options :: [Option]
options =
  [ enumOption ['d'] ["dump"] "PHASE" (undefined :: Phase) (\p f -> f { phases = Set.insert p (phases f) }) "dump internal data"
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
    _ -> mapM_ (hPutStr stderr) errors >> hPutStr stderr usage >> exitFailure
  flags <- foldM (\t s -> s t) defaults options

  f <- case args of
    [] -> putStrLn "Duck interactive mode" >. ""
    [file] -> return file
    _ -> fail "expected zero or one arguments"

  let ifv p = when (Set.member p (phases flags))
  let phase p io = do
        ifv p $ putStr ("\n-- "++pshow p++" --\n")
        r <- io
        ifv p $ pprint r
        return r
      phase' p = phase p . return

  ast <- phase PAst (loadModule Set.empty (path flags) f)
  ir <- phase PIr (Ir.prog ast)
  lir <- phase' PLir (Lir.prog ir)
  lir <- phase' PLink (Lir.union Prims.prelude lir)
  Lir.check lir
  lir <- phase PInfer (liftM fst $ runInfer [] Map.empty $ Infer.prog lir)
  env <- phase PEnv (runExec $ Interp.prog lir)

  unless (compileOnly flags) $ do
    unless (Set.null (phases flags)) $ putStr "\n-- Main --\n"
    Interp.main lir env

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
