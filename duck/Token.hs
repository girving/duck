-- | Duck tokens

module Token
  ( Token(..)
  , showAt
  ) where

import Pretty
import Var

data Token
  = TokVar { tokVar :: !Var }
  | TokCVar { tokVar :: !Var }
  | TokSym { tokVar :: !Var }
  | TokCSym { tokVar :: !Var }
  | TokInt { tokInt :: !Int }
  | TokChr { tokChr :: !Char }
  | TokEq
  | TokLP
  | TokRP
  | TokLB
  | TokRB
    -- In the following, Just t means an implicit token inserted before t
    -- by layout, and Nothing means a real token that appeared in the source.
  | TokLC !(Maybe Token)
  | TokRC !(Maybe Token)
  | TokSemi !(Maybe Token)
  | TokDColon
  | TokComma
  | TokDef
  | TokLet
  | TokData
  | TokIn
  | TokCase
  | TokOf
  | TokIf
  | TokThen
  | TokElse
  | TokAny
  | TokLambda
  | TokArrow
  | TokOr
  | TokMinus
  | TokImport
  | TokInfix { tokFix :: !Fixity }
  | TokComment
  | TokCommentEnd
  | TokEOF
  deriving Eq

instance Pretty Token where
  pretty t = pretty $ case t of
    TokVar (V v) -> v
    TokCVar (V v) -> v
    TokSym (V v) -> v
    TokCSym (V v) -> v
    TokInt i -> show i
    TokChr c -> show c
    TokDef -> "def"
    TokLet -> "let"
    TokData -> "data"
    TokIn -> "in"
    TokCase -> "case"
    TokOf -> "of"
    TokIf -> "if"
    TokThen -> "then"
    TokElse -> "else"
    TokImport -> "import"
    TokInfix LeftFix -> "infixl"
    TokInfix RightFix -> "infixr"
    TokInfix NonFix -> "infix"
    TokEq -> "="
    TokLP -> "("
    TokRP -> ")"
    TokLB -> "["
    TokRB -> "]"
    TokLC _ -> "{"
    TokRC _ -> "}"
    TokSemi _ -> ";"
    TokDColon -> ":"
    TokComma -> ","
    TokAny -> "_"
    TokLambda -> "\\"
    TokArrow -> "->"
    TokOr -> "|"
    TokMinus -> "-"
    TokComment -> "{-"
    TokCommentEnd -> "-}"
    TokEOF -> "<eof>"

showAt :: Token -> String
showAt (TokLC (Just t)) = "before "++qshow t
showAt (TokRC (Just t)) = "before "++qshow t
showAt (TokSemi (Just t)) = "before "++qshow t
showAt t = "at "++qshow t
