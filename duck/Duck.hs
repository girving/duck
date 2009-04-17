-- Duck interpreter

module Main where

import Lex
import Parse
import Pretty
import System.Environment
import qualified Ir
import qualified Interp

header = "Duck interactive mode"

newline = putStrLn ""

main = do
  args <- getArgs
  code <- case args of
    [] -> do
      putStrLn header
      getContents
    [file] -> readFile file
    _ -> error "expected zero or one arguments"

  putStr "\n-- AST --\n"
  let ast = parse $ lexer code
  pprint ast

  putStr "\n-- IR --\n"
  let ir = Ir.prog ast
  pprint ir

  putStr "\n-- Result --\n"
  let env = Interp.prog ir
  pprint env
