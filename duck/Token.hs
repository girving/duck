-- | Duck tokens

module Token
  ( Token(..)
  , Fixity(..)
  , showAt
  ) where

import Pretty
import Var

data Fixity = LeftFix | NonFix | RightFix deriving (Eq, Show, Ord)

data Token
  = TokVar { tokVar :: !Var }
  | TokCVar { tokVar :: !Var }
  | TokSym { tokVar :: !Var }
  | TokCSym { tokVar :: !Var }
  | TokInt { tokInt :: !Int }
  | TokChar { tokChar :: !Char }
  | TokString { tokString :: !String }
  | TokEq
  | TokLP
  | TokRP
  | TokLB
  | TokRB
    -- In the following, Just t means an implicit token inserted before/after t
    -- by layout, and Nothing means a real token that appeared in the source.
  | TokLC { tokImplicit :: !(Maybe Token) }
  | TokRC { tokImplicit :: !(Maybe Token) }
  | TokSemi { tokImplicit :: !(Maybe Token) }
  | TokDColon
  | TokComma
  | TokLet { tokStatic :: !Bool }
  | TokData
  | TokIn
  | TokCase { tokStatic :: !Bool }
  | TokOf
  | TokIf { tokStatic :: !Bool }
  | TokThen
  | TokElse
  | TokAny
  | TokGroup
  | TokArrow
  | TokMinus
  | TokImport
  | TokInfix { tokFix :: !Fixity }
  | TokComment
  | TokCommentEnd
  | TokSOF
  | TokEOF
  deriving Eq

instance Pretty Fixity where
  pretty LeftFix = pretty "infixl"
  pretty RightFix = pretty "infixr"
  pretty NonFix = pretty "infix"

instance Pretty Token where
  pretty t = pretty $ case t of
    TokVar (V v) -> v
    TokCVar (V v) -> v
    TokSym (V v) -> v
    TokCSym (V v) -> v
    TokInt i -> show i
    TokChar c -> show c
    TokString s -> show s
    TokLet s -> sStatic s "let"
    TokData -> "data"
    TokIn -> "in"
    TokCase s -> sStatic s "case"
    TokOf -> "of"
    TokIf s -> sStatic s "if"
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
    TokDColon -> "::"
    TokComma -> ","
    TokAny -> "_"
    TokGroup -> "\\"
    TokArrow -> "->"
    TokMinus -> "-"
    TokComment -> "{-"
    TokCommentEnd -> "-}"
    TokSOF -> "<sof>"
    TokEOF -> "<eof>"

showAt :: Token -> String
showAt (TokLC (Just t)) = "before "++qout t
showAt (TokRC (Just t)) = "after "++qout t
showAt (TokSemi (Just t)) = "before "++qout t
showAt t = "at "++qout t
