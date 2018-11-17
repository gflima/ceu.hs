module Ceu.Grammar.Check where

import Ceu.Grammar
import qualified Ceu.Grammar.Check.Loop   as Loop
import qualified Ceu.Grammar.Check.Escape as Escape

tight :: Stmt -> [(String,Stmt)]
tight p = mapmsg "invalid statement" (tight' (-1) p)
tight' _ s@(AwaitInt _) = [s]
tight' _ s@(AwaitExt _) = [s]
tight' n s@(Every _ p)  = [s] ++ tight' n p
tight' n s@(Fin p)      = [s] ++ tight' n p
tight' n s@(Loop p)     = tight' n p
tight' n (Var _ p)      = tight' n p
tight' n (Int _ p)      = tight' n p
tight' n (If _ p q)     = tight' n p ++ tight' n q
tight' n (Seq p q)      = tight' n p ++ tight' n q
tight' n s@(Par p q)    = [s] ++ tight' n p ++ tight' n q
tight' n s@(Pause _ p)  = [s] ++ tight' n p
tight' n (Trap p)       = tight' (n+1) p
tight' n s@(Escape k)
  | (n >= k)  = [s]
  | otherwise = [s]
tight' _ _              = []

-- Checks if program is valid.
-- Returns all statements that fail.

stmts :: Stmt -> [(String,Stmt)]
stmts stmt = case stmt of
  Var _ p       -> stmts p
  Int _ p       -> stmts p
  If _ p q      -> stmts p ++ stmts q
  Seq p q       -> stmts p ++ stmts q
  s@(Loop p)    -> stmts p ++ (if (Loop.check (Loop p)) then [] else [("unbounded `loop` execution", s)])
  s@(Every e p) -> stmts p ++ (aux "invalid statement in `every`" s p)
  Par p q       -> stmts p ++ stmts q
  Pause _ p     -> stmts p
  s@(Fin p)     -> stmts p ++ (aux "invalid statement in `finalize`" s p)
  Trap p        -> stmts p
  _             -> []

aux msg s p =
  let ret = tight p in
    if (ret == []) then
      []
    else
      [(msg, s)] ++ ret

check :: Stmt -> [(String,Stmt)]
check p = (stmts p) ++ (Escape.check p)

go :: Stmt -> Stmt
go p
  | check p == [] = p
  | otherwise   = error "invalid program"
