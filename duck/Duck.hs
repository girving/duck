-- Duck interpreter

module Main where

import Lex
import Parse
import System.Environment
import Ast

header = "Duck interactive mode"

main = do
  args <- getArgs
  code <- case args of
    [] -> do
      putStrLn header
      getContents
    [file] -> readFile file
    _ -> error "expected zero or one arguments"
  let ast = parse $ lexer code
  print $ ast
  print $ pretty ast
