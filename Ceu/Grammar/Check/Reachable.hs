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
    x = if (infinite p1 || (not $ neverEscapes p1)) then [err_stmt_msg p2 "unreachable statement"] else []
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

infinite :: Stmt -> Bool
infinite (Var _ p)      = neverEscapes p && infinite p
infinite (Int _ p)      = neverEscapes p && infinite p
infinite (AwaitExt ext) = ext == "FOREVER"
infinite (If _ p1 p2)   = neverEscapes p1 && neverEscapes p2 && infinite p1 && infinite p2
infinite (Seq p1 p2)    = neverEscapes p1 && (infinite p1 || (neverEscapes p2 && infinite p2))
infinite (Loop p)       = neverEscapes p
infinite (Every _ p)    = True
infinite (Par p1 p2)    = neverEscapes p1 && neverEscapes p2 && (infinite p1 || infinite p2)
infinite (Pause _ p)    = neverEscapes p && infinite p
infinite (Fin p)        = True
infinite (Trap p)       = neverEscapes p && infinite p
infinite _              = False
