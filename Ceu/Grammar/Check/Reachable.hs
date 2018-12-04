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
check s = case getStmt' s of
  (Var _ p)    -> (check p)
  (Int _ p)    -> (check p)
  (If _ p1 p2) -> (check p1) ++ (check p2)
  (Seq p1 p2)  -> (check p1) ++ x ++ (check p2)
    where
      x = if (neverTerminates p1) then [err_stmt_msg p2 "unreachable statement"]
                                  else []
  (Loop p)     -> err ++ (check p) where
                  err = if neverTerminates p then [err_stmt_msg s "`loop` never iterates"]
                                             else []
  (Every _ p)  -> (check p)
  (Par p1 p2)  -> (check p1) ++ (check p2)
  (Pause _ p)  -> (check p)
  (Fin p)      -> (check p)
  (Trap p)     -> (check p)
  otherwise    -> []

-------------------------------------------------------------------------------

neverTerminates :: Stmt -> Bool
neverTerminates s = case getStmt' s of
  (Var _ p)            -> neverTerminates p
  (Int _ p)            -> neverTerminates p
  (AwaitExt "FOREVER") -> True
  (If _ p1 p2)         -> neverTerminates p1 && neverTerminates p2
  (Seq p1 p2)          -> neverTerminates p1 || neverTerminates p2
  (Loop p)             -> True
  (Every _ p)          -> True
  (Par p1 p2)          -> True
  (Pause _ p)          -> neverTerminates p
  (Fin p)              -> True
  (Trap p)             -> not $ escapesAt1 p
  (Escape _)           -> True
  otherwise            -> False

maybeTerminates = not . neverTerminates

alwaysTerminates :: Stmt -> Bool
alwaysTerminates s = case getStmt' s of
  (Var _ p)            -> alwaysTerminates p
  (Int _ p)            -> alwaysTerminates p
  (AwaitExt "FOREVER") -> False
  (If _ p1 p2)         -> alwaysTerminates p1 && alwaysTerminates p2
  (Seq p1 p2)          -> alwaysTerminates p1 && alwaysTerminates p2
  (Loop p)             -> False
  (Every _ p)          -> False
  (Par p1 p2)          -> False
  (Pause _ p)          -> alwaysTerminates p
  (Fin p)              -> False
  (Trap p)             -> escapesAt1 p
  (Escape _)           -> False
  otherwise            -> True
