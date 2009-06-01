-- Duck interpreter

module Main where

import Parse
import ParseMonad
import Pretty
import System.Environment
import System.FilePath
import qualified Ir
import qualified Interp
import ExecMonad
import Control.Monad

header = "Duck interactive mode"

newline = putStrLn ""

main = do
  args <- getArgs
  (file,code) <- case args of
    [] -> do
      putStrLn header
      c <- getContents
      return ("<stdin>",c)
    [file] -> do
      c <- readFile file
      return (dropExtension file, c)
    _ -> error "expected zero or one arguments"

  let ifv = when False

  ifv $ putStr "\n-- AST --\n"
  ast <- runP parse file code
  ifv $ pprint ast

  ifv $ putStr "\n-- IR --\n"
  let ir = Ir.prog ast
  ifv $ pprint ir

  ifv $ putStr "\n-- Environment --\n"
  env <- runExec (Interp.prog ir)
  ifv $ pprint env

  ifv $ putStr "\n-- Main --\n"
  Interp.main env

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
