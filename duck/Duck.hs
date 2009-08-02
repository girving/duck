-- | Duck interpreter

module Main where

import Parse
import ParseMonad
import Pretty
import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.IO
import System.Exit
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
  , compileOnly :: Bool }
type Option = OptDescr (Flags -> IO Flags)

enumOption :: (Pretty e, Enum e, Bounded e) => [Char] -> [String] -> String -> e -> (e -> Flags -> Flags) -> String -> Option
enumOption short long name _ f help = Option short long (ReqArg process name) help' where
  help' = help ++ " (one of " ++ concat (intersperse ", " (map (show . pretty) values)) ++ ")"
  values = enumFrom minBound
  process :: String -> Flags -> IO Flags
  process s flags = case lookup s [(show (pretty x),x) | x <- values] of
    Nothing -> die ("invalid argument "++s++" to --"++head long)
    Just x -> return (f x flags)

options :: [Option]
options =
  [ enumOption ['d'] ["dump"] "PHASE" (undefined :: Phase) (\p f -> f { phases = Set.insert p (phases f) }) "dump internal data"
  , Option ['c'] [] (NoArg $ \f -> return $ f { compileOnly = True }) "compile only, don't evaluate main"
  , Option ['h'] ["help"] (NoArg $ \_ -> putStr usage >> exitSuccess) "show this help" ]
usage = usageInfo "duck [options] [files...]" options

defaults = Flags
  { phases = Set.empty
  , compileOnly = False }

main = do
  (options, args, errors) <- getOpt Permute options =.< getArgs
  case errors of
    [] -> return ()
    _ -> mapM_ (hPutStr stderr) errors >> hPutStr stderr usage >> exitFailure
  flags <- foldM (\t s -> s t) defaults options

  (file,code) <- case args of
    [] -> do
      putStrLn "Duck interactive mode"
      c <- getContents
      return ("<stdin>",c)
    [file] -> do
      c <- readFile file
      return (dropExtension file, c)
    _ -> error "expected zero or one arguments"

  let ifv p = when (Set.member p (phases flags))
  let phase p io = do
        ifv p $ putStr ("\n-- "++show (pretty p)++" --\n")
        r <- io
        ifv p $ pprint r
        return r
      phase' p = phase p . return

  prelude <- Prims.prelude

  ast <- phase PAst (runP parse file code)
  ir <- phase PIr (Ir.prog ast)
  lir <- phase PLir (Lir.prog ir)
  lir <- phase' PLink (Lir.union prelude lir)
  info <- phase PInfer (runInfer Map.empty $ Infer.prog lir)
  env <- phase PEnv (runExec info $ Interp.prog lir)

  unless (compileOnly flags) $ do
    unless (Set.null (phases flags)) $ putStr "\n-- Main --\n"
    Interp.main lir env info

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
