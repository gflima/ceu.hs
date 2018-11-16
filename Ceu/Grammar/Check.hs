module Ceu.Grammar.Check where

import Ceu.Grammar
import qualified Ceu.Grammar.Check.Loop   as Loop
import qualified Ceu.Grammar.Check.Escape as Escape

tight :: Stmt -> Bool
tight (AwaitInt _)   = False
tight (AwaitExt _)   = False
tight (Every _ _)    = False
tight (Fin _)        = False
tight (Loop _)       = False
tight (Var _ p)      = tight p
tight (Int _ p)      = tight p
tight (If _ p q)     = tight p && tight q
tight (Seq p q)      = tight p && tight q
tight (Par p q)      = False
tight (Pause _ p)    = False
tight (Trap p)       = tight p
tight (Escape _)     = False
tight _              = True

-- Checks if program is valid.
-- Returns all statements that fail.

stmts :: Stmt -> [Stmt]
stmts stmt = case stmt of
  Var _ p       -> stmts p
  Int _ p       -> stmts p
  If _ p q      -> stmts p ++ stmts q
  Seq p q       -> stmts p ++ stmts q
  s@(Loop p)    -> stmts p ++ (if (Loop.check (Loop p)) then [] else [s])
  s@(Every e p) -> stmts p ++ (if (tight p) then [] else [s])
  Par p q       -> stmts p ++ stmts q
  Pause _ p     -> stmts p
  s@(Fin p)     -> stmts p ++ (if (tight p) then [] else [s])
  Trap p        -> stmts p
  _             -> []

check :: Stmt -> [Stmt]
check p = (stmts p) ++ (Escape.check p)

go :: Stmt -> Stmt
go p
  | check p == [] = p
  | otherwise   = error "invalid program"
