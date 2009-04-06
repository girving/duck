-- Duck interpreter

module Main where

import Lex
import Parse

main = getContents >>= print. parse . lexer
