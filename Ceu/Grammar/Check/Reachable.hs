module Ceu.Grammar.Check.Reachable where

import Ceu.Globals
import Ceu.Grammar
import Ceu.Grammar.Check.Escape (escapes)

-- Looks for unreachable statements:
--  escape 0 ; ...
--  awaitFor ; ...
--  every    ; ...
--  loop/inf ; ...
--  par/inf  ; ...
-- Returns all errors found.

check :: Stmt -> Errors
check (Var _ p)    = (check p)
check (Int _ p)    = (check p)
check (If _ p1 p2) = (check p1) ++ (check p2)
check (Seq p1 p2)  = (check p1) ++ x ++ (check p2)
  where
    x = if (infinite p1 || (escapes p1 /= [])) then [err_stmt_msg p2 "unreachable statement"] else []
check (Loop p)     = (check p)
check (Every _ p)  = (check p)
check (Par p1 p2)  = (check p1) ++ (check p2)
check (Pause _ p)  = (check p)
check (Fin p)      = (check p)
check (Trap p)     = (check p)
check p            = []

noEscapes p = (escapes p == [])

infinite :: Stmt -> Bool
infinite (Var _ p)      = noEscapes p && infinite p
infinite (Int _ p)      = noEscapes p && infinite p
infinite (AwaitExt ext) = ext == "FOREVER"
infinite (If _ p1 p2)   = noEscapes p1 && noEscapes p2 && infinite p1 && infinite p2
infinite (Seq p1 p2)    = noEscapes p1 && (infinite p1 || (noEscapes p2 && infinite p2))
infinite (Loop p)       = noEscapes p
infinite (Every _ p)    = True
infinite (Par p1 p2)    = noEscapes p1 && noEscapes p2 && (infinite p1 || infinite p2)
infinite (Pause _ p)    = noEscapes p && infinite p
infinite (Fin p)        = True
infinite (Trap p)       = noEscapes p && infinite p
infinite _              = False
