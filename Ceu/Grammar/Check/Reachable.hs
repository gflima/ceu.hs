module Ceu.Grammar.Check.Reachable where

import Ceu.Globals
import Ceu.Grammar
import Ceu.Grammar.Check.Escape (neverEscapes, escapesAt1)
import Debug.Trace

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
    x = if (neverTerminates p1) then [err_stmt_msg p2 "unreachable statement"] else []
check (Loop p)     = (check p)
check (Every _ p)  = (check p)
check (Par p1 p2)  = (check p1) ++ (check p2)
check (Pause _ p)  = (check p)
check (Fin p)      = (check p)
check (Trap p)     = (check p)
check p            = []

maybeTerminates :: Stmt -> Bool
maybeTerminates (Var _ p)            = maybeTerminates p
maybeTerminates (Int _ p)            = maybeTerminates p
maybeTerminates (AwaitExt "FOREVER") = False
maybeTerminates (If _ p1 p2)         = maybeTerminates p1 || maybeTerminates p2
maybeTerminates (Seq p1 p2)          = maybeTerminates p1 && maybeTerminates p2
maybeTerminates (Loop p)             = False
maybeTerminates (Every _ p)          = False
maybeTerminates (Par p1 p2)          = maybeTerminates p1 && maybeTerminates p2
maybeTerminates (Pause _ p)          = maybeTerminates p
maybeTerminates (Fin p)              = False
maybeTerminates (Trap p)             = escapesAt1 p || maybeTerminates p
maybeTerminates (Escape _)           = False
maybeTerminates _                    = True

neverTerminates :: Stmt -> Bool
neverTerminates (Var _ p)            = neverTerminates p
neverTerminates (Int _ p)            = neverTerminates p
neverTerminates (AwaitExt "FOREVER") = True
neverTerminates (If _ p1 p2)         = neverTerminates p1 && neverTerminates p2
neverTerminates (Seq p1 p2)          = neverTerminates p1 || neverTerminates p2
neverTerminates (Loop p)             = True
neverTerminates (Every _ p)          = True
neverTerminates (Par p1 p2)          = neverTerminates p1 || neverTerminates p2
neverTerminates (Pause _ p)          = neverTerminates p
neverTerminates (Fin p)              = True
neverTerminates (Trap p)             = not $ escapesAt1 p
neverTerminates (Escape _)           = True
neverTerminates _                    = False
