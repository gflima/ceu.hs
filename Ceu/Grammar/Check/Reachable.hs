module Ceu.Grammar.Check.Reachable where

import Ceu.Grammar.Globals
import Ceu.Grammar.Stmt
import Ceu.Grammar.Check.Escape (neverEscapes, escapesAt1)
import Debug.Trace
import Control.Exception

-- Looks for unreachable statements:
--  escape 0 ; ...
--  awaitFor ; ...
--  every    ; ...
--  loop     ; ...
--  par/inf  ; ...
-- Looks for loop bodies that do not terminate:
--  loop awaitFor end
-- Returns all errors found.

check :: Stmt -> Errors
check (Var _ p)    = (check p)
check (Int _ p)    = (check p)
check (If _ p1 p2) = (check p1) ++ (check p2)
check (Seq p1 p2)  = (check p1) ++ x ++ (check p2)
  where
    x = if (neverTerminates p1) then [err_stmt_msg p2 "unreachable statement"] else []
check s@(Loop p)   = err ++ (check p) where
                       err = if neverTerminates p then
                         [err_stmt_msg s "`loop` never iterates"]
                       else
                         []
check (Every _ p)  = (check p)
check (Par p1 p2)  = (check p1) ++ (check p2)
check (Pause _ p)  = (check p)
check (Fin p)      = (check p)
check (Trap p)     = (check p)
check p            = []

-------------------------------------------------------------------------------

neverTerminates :: Stmt -> Bool
neverTerminates (Var _ p)            = neverTerminates p
neverTerminates (Int _ p)            = neverTerminates p
neverTerminates (AwaitExt "FOREVER") = True
neverTerminates (If _ p1 p2)         = neverTerminates p1 && neverTerminates p2
neverTerminates (Seq p1 p2)          = neverTerminates p1 || neverTerminates p2
neverTerminates (Loop p)             = True
neverTerminates (Every _ p)          = True
neverTerminates (Par p1 p2)          = True
neverTerminates (Pause _ p)          = neverTerminates p
neverTerminates (Fin p)              = True
neverTerminates (Trap p)             = not $ escapesAt1 p
neverTerminates (Escape _)           = True
neverTerminates _                    = False

maybeTerminates = not . neverTerminates

alwaysTerminates :: Stmt -> Bool
alwaysTerminates (Var _ p)            = alwaysTerminates p
alwaysTerminates (Int _ p)            = alwaysTerminates p
alwaysTerminates (AwaitExt "FOREVER") = False
alwaysTerminates (If _ p1 p2)         = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Seq p1 p2)          = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Loop p)             = False
alwaysTerminates (Every _ p)          = False
alwaysTerminates (Par p1 p2)          = False
alwaysTerminates (Pause _ p)          = alwaysTerminates p
alwaysTerminates (Fin p)              = False
alwaysTerminates (Trap p)             = escapesAt1 p
alwaysTerminates (Escape _)           = False
alwaysTerminates _                    = True
