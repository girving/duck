{-# LANGUAGE ScopedTypeVariables #-}
-- | Duck interpreter

module Main (main, run) where

import qualified Data.ByteString.Lazy as BS
import Data.Functor
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad 
import Control.Monad.Trans.Maybe
import System.Environment
import System.FilePath
import System.Directory
import System.Console.GetOpt
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

data Options = Options
  { optionHelp        :: Maybe [String]
  , optionDumpStages  :: Set Stage
  , optionLastStage   :: Stage
  , optionHaskell     :: Bool
  , optionIncludes    :: [FilePath]
  }

defaultOptions :: Options
defaultOptions = Options
  { optionHelp        = Nothing
  , optionDumpStages  = Set.empty
  , optionLastStage   = maxBound
  , optionHaskell     = False
  , optionIncludes    = [""]
  }

type Option = OptDescr (Options -> Options)

optionErrors :: Options -> [String]
optionErrors = fromMaybe [] . optionHelp

optionError :: String -> Options -> Options
optionError s o = o{ optionHelp = Just $ optionErrors o ++ [s] }

enumOption :: Enum e => [Char] -> [String] -> String -> [String] -> (e -> Options -> Options) -> String -> Option
enumOption short long name choices f help = Option short long (ReqArg process name) help' where
  help' = help ++ " (" ++ intercalate "," choices ++ ")"
  process p = case findIndices (p `isPrefixOf`) choices of
    [e] -> f (toEnum e)
    [] -> optionError $ "Unknown " ++ name ++ ". Choices are: " ++ intercalate "," choices
    l -> optionError $ "Ambiguous " ++ name ++ ". Choices are: " ++ intercalate "," (map (choices !!) l)

options :: [Option]
options =
  [ Option     ['h'] ["help"]    (NoArg $ \o -> o { optionHelp = Just $ optionErrors o }) 
      "show this help" 
  , enumOption ['d'] ["dump"]    "PHASE" stageNames (\p o -> o { optionDumpStages = Set.insert p (optionDumpStages o) }) 
      "dump internal data after PHASE"
  , Option     ['c'] []          (NoArg $ \o -> o { optionLastStage = pred (optionLastStage o) }) 
      "compile only, don't evaluate main"
  , Option     []    ["haskell"] (NoArg $ \o -> o { optionHaskell = True }) 
      "generate equivalent Haskell code from AST"
  , Option     ['I'] ["include"] (ReqArg (\p o -> o { optionIncludes = optionIncludes o ++ [p] }) "DIRECTORY") 
      "add DIRECTORY to module search path"
  ]

usage :: String
usage = usageInfo "duck [OPTIONS] [FILE]" options

findModule :: [FilePath] -> ModuleName -> MaybeT IO FilePath
findModule l s = do
  let ext = ".duck"
      f | takeExtension s == ext = s
        | otherwise = addExtension s (tail ext)
  msum $ map (MaybeT . (\p -> doesFileExist p >.= \e -> guard e >. p) . (</> f)) l

loadModule :: Set ModuleName -> [FilePath] -> ModuleName -> IO [(ModuleName, Ast.Prog)]
loadModule s l m = do
  (f,c) <- case m of
    "" -> (,) "<stdin>" <$> BS.getContents
    m -> runMaybeT (findModule l m) >>= maybe 
      (fatalIO $ msg ("module" <+> quoted m <+> "not found"))
      (\f -> (,) (dropExtension f) <$> BS.readFile f)
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
  (options, args, errors) <- getOpt Permute options <$> getArgs
  when (not (null errors)) $
    die 2 $ concat errors ++ usage
  let opts = foldl' (flip ($)) defaultOptions options
  case optionHelp opts of
    Nothing -> nop
    Just [] -> putStr usage >> exitSuccess
    Just e -> die 2 $ intercalate "\n" e

  f <- case args of
    [] -> putStrLn "Duck interactive mode" >. ""
    [file] -> return file
    _ -> fail "expected zero or one arguments"

  let 
    phase p pf io = if p > optionLastStage opts then return undefined else do
      let ifv = when (p `Set.member` optionDumpStages opts)
      ifv $ putStrLn ("\n-- "++pout p++" --")
      r <- runStage p io
      ifv $ pout $ pf r
      return r
    phase' p pf = phase p pf . evaluate

  ast <- phase StageParse (concatMap snd) $ loadModule Set.empty (optionIncludes opts) f
  when (optionHaskell opts) $ do
    putStrLn $ pout $ uncurry ToHaskell.prog $ last ast
    exitSuccess

  ir <- phase' StageIr (concatMap snd) $ snd $ mapAccumL (uncurry . Ir.prog) Map.empty ast
  lir <- phase' StageLir id $ ToLir.progs Base.base ir
  _ <- phase' StageLink (const ()) $ Lir.check lir
  lir <- phase StageInfer id $ runInferProg Infer.prog lir
  _ <- phase StageExec (\v -> (Map.map fst $ Lir.progGlobalTypes lir, v)) $ runExec lir Interp.prog
  nop

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
