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

check :: (Stmt ann) -> Errors
check (Var _ _ p)    = (check p)
check (Int _ _ p)    = (check p)
check (If _ _ p1 p2) = (check p1) ++ (check p2)
check (Seq _ p1 p2)  = (check p1) ++ x ++ (check p2)
  where
    x = if (neverTerminates p1) then [err_stmt_msg p2 "unreachable statement"] else []
check s@(Loop _ p)   = err ++ (check p) where
                       err = if neverTerminates p then
                         [err_stmt_msg s "`loop` never iterates"]
                       else
                         []
check (Every _ _ p)  = (check p)
check (Par _ p1 p2)  = (check p1) ++ (check p2)
check (Pause _ _ p)  = (check p)
check (Fin _ p)      = (check p)
check (Trap _ p)     = (check p)
check p              = []

-------------------------------------------------------------------------------

neverTerminates :: (Stmt ann) -> Bool
neverTerminates (Var _ _ p)            = neverTerminates p
neverTerminates (Int _ _ p)            = neverTerminates p
neverTerminates (AwaitExt _ "FOREVER") = True
neverTerminates (If _ _ p1 p2)         = neverTerminates p1 && neverTerminates p2
neverTerminates (Seq _ p1 p2)          = neverTerminates p1 || neverTerminates p2
neverTerminates (Loop _ p)             = True
neverTerminates (Every _ _ p)          = True
neverTerminates (Par _ p1 p2)          = True
neverTerminates (Pause _ _ p)          = neverTerminates p
neverTerminates (Fin _ p)              = True
neverTerminates (Trap _ p)             = not $ escapesAt1 p
neverTerminates (Escape _ _)           = True
neverTerminates _                      = False

maybeTerminates = not . neverTerminates

alwaysTerminates :: (Stmt ann) -> Bool
alwaysTerminates (Var _ _ p)            = alwaysTerminates p
alwaysTerminates (Int _ _ p)            = alwaysTerminates p
alwaysTerminates (AwaitExt _ "FOREVER") = False
alwaysTerminates (If _ _ p1 p2)         = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Seq _ p1 p2)          = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Loop _ p)             = False
alwaysTerminates (Every _ _ p)          = False
alwaysTerminates (Par _ p1 p2)          = False
alwaysTerminates (Pause _ _ p)          = alwaysTerminates p
alwaysTerminates (Fin _ p)              = False
alwaysTerminates (Trap _ p)             = escapesAt1 p
alwaysTerminates (Escape _ _)           = False
alwaysTerminates _                      = True
