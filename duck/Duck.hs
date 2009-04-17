-- Duck interpreter

module Main where

import Lex
import Parse
import Pretty
import System.Environment
import qualified Ir

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
  let ast = parse $ lexer code
  print ast
  newline
  print $ pretty ast
  newline
  let ir = Ir.prog ast
  print $ pretty ir
