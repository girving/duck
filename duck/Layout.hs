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

layout :: P (Loc Token) -> P (Loc Token)
layout lex = do
  state <- get
  Loc loc token <- lex -- grab the next token
  case (token, ps_comment state) of
    (TokComment, c) -> do
      modify $ \s -> s{ ps_comment = loc : c }
      layout lex
    (TokCommentEnd, _:c) -> do
      modify $ \s -> s{ ps_comment = c }
      layout lex
    _ -> do
      layout' state loc token

  where
  layout' :: ParseState -> SrcLoc -> Token -> P (Loc Token)
  layout' s@(ParseState{ ps_comment = c:_ }) _ TokEOF = psError s $ "unterminated comment starting" <+> c
  layout' s@(ParseState{ ps_comment = _:_ }) _ tok = psError s $ "unexpected token" <+> quoted tok <+> "in comment"
  layout' state loc token = (if ps_start state then start else normal) token (ps_layout state) where

    push :: Context -> P ()
    push m = modify $ \s -> s
      { ps_layout = m : ps_layout s
      , ps_start = False }

    -- Slight name abuse, since pop takes the new stack as an argument.
    -- However, the name 'pop' makes for nice documentation
    pop :: [Context] -> P ()
    pop ms = modify $ \s -> s { ps_layout = ms }

    -- Advance ps_last to the current line
    advance :: P ()
    advance = modify $ \s -> s { ps_last = loc }

    -- Accept the next explicit token
    accept :: P (Loc Token)
    accept = do
      case token of
        TokOf -> modify $ \s -> s { ps_start = True }
        TokLC _ -> push (Explicit loc)
        _ -> nop
      advance >. Loc loc token

    -- Inject an extra token before the next explicit one and rewind
    -- the parse state so that the next real token is seen again.
    inject :: (Maybe Token -> Token) -> P (Loc Token)
    inject t = do
      modify $ \s -> s
        { ps_loc = ps_loc state
        , ps_rest = ps_rest state
        , ps_prev = ps_prev state }
      return $ Loc loc (t $ Just token)

    -- |start is called after the beginning of the file or after \'of\', and
    -- inserts an implicit '{' if an explicit one is not given.
    start :: Token -> [Context] -> P (Loc Token)
    start (TokLC _) _ = accept -- found an explicit '{', so push an explicit context
    start _ ms -- no '{', so we need to insert one
      | srcCol loc > top ms = push (Implicit (beforeLoc loc) (srcCol loc)) >> advance >> inject TokLC -- we're to the left of the enclosing context, so insert '{' and push implicit context
      | otherwise = push (Implicit (beforeLoc loc) maxBound) >> inject TokLC -- otherwise insert '{' with a location such that '}' will be inserted immediately after

    normal :: Token -> [Context] -> P (Loc Token)
    normal (TokRC _) (Explicit _:ms) = pop ms >> accept -- found '}' in an explicit context, so pop
    normal (TokRC _) (Implicit _ _:ms) = pop ms >> inject TokRC -- found '}' in implicit, so escape back to enclosing explicit
    normal TokEOF (Implicit _ _:ms) = pop ms >> inject TokRC -- end of file reached inside implicit context, add a '}'
    normal TokEOF (Explicit l:_) = layoutError ("unmatched '{' at "++show l)
    normal _ (m:ms) | sameLine (ps_last state) loc = accept -- another token on the same line
                      -- otherwise, we're at the first token on a new line
                    | srcCol loc == col m = advance >> inject TokSemi -- indented equally, add a ';'
                    | srcCol loc < col m = pop ms >> inject TokRC -- indented less, pop the enclosing context and repeat
                    | otherwise = accept -- indented more or enclosing context is explicit, so do nothing
    normal _ [] = accept -- nothing to do

    -- |Column number corresponding to context.  Explicit contexts are considered to begin at column 0.
    col :: Context -> Int
    col (Explicit _) = 0
    col (Implicit _ c) = c

    -- |Column number of innermost context
    top :: [Context] -> Int
    top (m:_) = col m
    top [] = -1

    layoutError :: String -> P a
    layoutError s = psError state ("layout error: "++s)
