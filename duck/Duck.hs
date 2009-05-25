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

  putStr "\n-- AST --\n"
  ast <- runP parse file code
  pprint ast

  putStr "\n-- IR --\n"
  let ir = Ir.prog ast
  pprint ir

  putStr "\n-- Result --\n"
  env <- runExec (Interp.prog ir)
  pprint env

-- for ghci use
run :: String -> IO ()
run file = withArgs [file] main
