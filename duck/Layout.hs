-- | Duck Layout (whitespace dependent syntax)
--
-- The layout pass occurs between lexing and parsing, and inserts extra braces
-- and semicolons to make grouping explicit.  Duck layout follows the Haskell
-- layout defined in
-- <http://www.haskell.org/onlinereport/lexemes.html#lexemes-layout> and
-- <http://www.haskell.org/onlinereport/syntax-iso.html#layout>.  Layout takes
-- effect after \'of\' or at the beginning of the file if the next token isn't '{'.
--
-- I think layout rules want to be a bit different for \'let\' than for \'of\' since
-- \'let\' has a different structure.  For now we solve this by restricting \'let\'
-- to declare only one variable at a time, so layout doesn't apply.
--
-- For now, we also skip the \"parse error means insert '}' rule\".


module Layout 
  ( layout
  ) where

import Control.Monad.State

import Util
import Pretty
import Token
import SrcLoc
import ParseMonad

data Leader
  = Block
  | Mandatory
  | Optional

leaderType :: Token -> Maybe Leader
leaderType TokSOF = Just Block
leaderType TokOf = Just Mandatory
leaderType TokCase = Just Optional
leaderType TokEq = Just Optional
leaderType TokThen = Just Optional
leaderType TokElse = Just Optional
leaderType TokArrow = Just Optional
leaderType TokIn = Just Optional
leaderType _ = Nothing

push :: Context -> P ()
push c = modify $ \s -> s { ps_layout = c : ps_layout s }

pop :: P ()
pop = modify $ \s -> s { ps_layout = tail (ps_layout s) }

pltok :: Loc Token -> Doc'
pltok (Loc l t) = quoted t <+> ("at" <&+> l)

layout :: P (Loc Token) -> P (Loc Token)
layout lex = do
  state0 <- get
  tok <- lex -- grab the next token
  state <- get

  let
    input :: [Context] -> P (Loc Token)
    input [] = input [Context Outside (ps_last state) 0] -- fake outer context
    input (cc:_) = normal cc (fmap leaderType (ps_last state)) tok

    accept :: P (Loc Token)
    accept = modify (\s -> s{ ps_last = tok }) >. tok

    -- Inject an extra token over the given one and rewind
    -- the parse state so that the next real token is seen again.
    inject :: (Maybe Token -> Token) -> Loc Token -> P (Loc Token)
    inject f t = modify (\s -> s
      { ps_loc = ps_loc state0
      , ps_rest = ps_rest state0
      , ps_prev = ps_prev state0
      , ps_last = tok
      }) >. tok
      where tok = fmap (f . Just) t

    open :: ContextType -> Int -> P (Loc Token)
    open t c = push (Context t (ps_last state) c) >> inject TokLC tok

    break :: P (Loc Token)
    break = inject TokSemi tok

    close :: P (Loc Token)
    close = pop >> inject TokRC (ps_last state)

    normal :: Context -> Loc (Maybe Leader) -> Loc Token -> P (Loc Token)
    -- comments
    normal _ _ (Loc _ TokComment) = push (Context Comment tok 0) >> layout lex
    normal (Context Comment _ _) _ (Loc _ TokCommentEnd) = pop >> layout lex
    normal (Context Comment (Loc l _) _) _ tok = psError state $ "unexpected" <+> pltok tok <+> "in comment beginning" <+> l
    -- ends
    normal (Context Explicit _ _) _ (Loc _ (TokRC _)) = pop >> accept -- explicit close
    normal (Context Outside _ _)  _ (Loc _ (TokRC _)) = psError state $ "unmatched" <+> pltok tok
    normal _                      _ (Loc _ (TokRC _)) = close -- force implicit close
    normal (Context Explicit open _) _ (Loc _ TokEOF) = psError state $ "unmatched" <+> pltok open
    normal (Context Outside _ _)     _ (Loc _ TokEOF) = accept
    normal _                         _ (Loc _ TokEOF) = close -- force implicit close
    -- beginnings and middles
    normal _ _ (Loc _ (TokLC _)) = push (Context Explicit tok 0) >> accept -- explicit open
    normal _ (Loc _ (Just Block)) (Loc l _) = open ImplicitBlock (srcCol l) -- forced implicit open
    normal (Context _ _ c) (Loc l1 (Just Mandatory)) (Loc l2 _) | sameLine l1 l2 = open ImplicitLine c -- single-line open
    normal _               (Loc l1 _)                (Loc l2 _) | sameLine l1 l2 = accept -- nothing new here
    normal (Context ImplicitBlock _ c) _ (Loc l _) | srcCol l == c = break -- next line
    normal (Context _ _ c)             _ (Loc l _) | srcCol l <= c = close -- shift left
    normal _ (Loc _ (Just _)) (Loc l _) = open ImplicitBlock (srcCol l) -- multi-line open
    -- everything else
    normal _ _ _ = accept

  input (ps_layout state)
