module Ceu.Grammar.Check where

import Ceu.Globals
import Ceu.Grammar
import Ceu.Grammar.Simplify
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Reachable as Reachable

tight :: Stmt -> [String]
tight p = errs_stmts_msg_map (tight' (-1) p) "invalid statement"
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

stmts :: Stmt -> Errors
stmts stmt = case stmt of
  Var _ p       -> stmts p
  Int _ p       -> stmts p
  If _ p q      -> stmts p ++ stmts q
  Seq p q       -> stmts p ++ stmts q
  s@(Loop p)    -> stmts p ++ (if (Loop.check (Loop p)) then [] else [err_stmt_msg s "unbounded `loop` execution"])
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
      [err_stmt_msg s msg] ++ ret

check :: Stmt -> Errors
check p = (stmts p) ++ (Escape.check p) ++ (Reachable.check p)

data Result = Success Stmt | Fail Errors

go :: Stmt -> Result
go p =
  let p'   = simplify p
      errs = check p'
  in
    if errs == [] then
        Success p'
    else
        Fail errs
