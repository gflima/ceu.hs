module Ceu.Grammar.Check where

import Ceu.Grammar
import qualified Ceu.Grammar.Check.Loop   as Loop
import qualified Ceu.Grammar.Check.Fin    as Fin
import qualified Ceu.Grammar.Check.Every  as Every
import qualified Ceu.Grammar.Check.Escape as Escape

-- Checks if program is valid.
stmts :: Stmt -> Bool
stmts stmt = case stmt of
  Var _ p      -> stmts p
  Int _ p      -> stmts p
  If _ p q     -> stmts p && stmts q
  Seq p q      -> stmts p && stmts q
  Loop p       -> Loop.check (Loop p) && stmts p
  Every e p    -> Every.check (Every e p) && stmts p
  Par p q      -> stmts p && stmts q
  Pause _ p    -> stmts p
  Fin p        -> Fin.check (Fin p) && stmts p
  Trap p       -> stmts p
  _            -> True

all :: Stmt -> Stmt
all p
  | not (stmts p)        = error "checkProg: invalid program"
  | not (Escape.check p) = error "checkEscape: invalid program"
  | otherwise            = p

