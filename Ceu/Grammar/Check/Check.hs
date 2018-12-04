module Ceu.Grammar.Check.Check where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Stmt
import Ceu.Grammar.Simplify
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Reachable as Reachable
import qualified Ceu.Grammar.Check.VarEvt    as VarEvt

getTights :: Stmt -> [String]
getTights p = errs_stmts_msg_map (aux (-1) p) "invalid statement" where
  aux n s = case getStmt' s of
    (AwaitInt _)  -> [s]
    (AwaitExt _)  -> [s]
    (Every _ p)   -> [s] ++ aux n p
    (Fin p)       -> [s] ++ aux n p
    (Loop p)      -> aux n p
    (Var _ p)     -> aux n p
    (Int _ p)     -> aux n p
    (If _ p q)    -> aux n p ++ aux n q
    (Seq p q)     -> aux n p ++ aux n q
    (Par p q)     -> [s] ++ aux n p ++ aux n q
    (Pause _ p)   -> [s] ++ aux n p
    (Trap p)      -> aux (n+1) p
    (Escape k)
      | (n >= k)  -> [s]
      | otherwise -> [s]
    _             -> []

-- Checks if program is valid.
-- Returns all statements that fail.

stmts :: Stmt -> Errors
stmts s = case getStmt' s of
  Var _ p   -> stmts p
  Int _ p   -> stmts p
  If _ p q  -> stmts p ++ stmts q
  Seq p q   -> stmts p ++ stmts q
  Loop p    -> stmts p ++ es where
               es = if Loop.check s
                      then []
                      else [err_stmt_msg s "unbounded `loop` execution"]
  Every e p -> stmts p ++ (aux "invalid statement in `every`" s p)
  Par p q   -> es ++ stmts p ++ stmts q where
               es = if (Reachable.neverTerminates p) && (Reachable.neverTerminates q)
                      then []
                      else [err_stmt_msg s "terminating trail"]
  Pause _ p -> stmts p
  Fin p     -> stmts p ++ (aux "invalid statement in `finalize`" s p)
  Trap p    -> stmts p
  otherwise -> []
  where
    aux msg s p =
      let ret = getTights p in
        if (ret == []) then
          []
        else
          [err_stmt_msg s msg] ++ ret

type Options = (Bool,Bool)

compile :: Options -> Stmt -> (Errors,Stmt)
compile (o_simp,o_encl) p = (es3,p2) where
  p1       = if not o_encl then p else
              (newStmt$Var "_ret" (newStmt$Seq (newStmt$Trap p) (newStmt$AwaitExt "FOREVER")))
  p2       = if not o_simp then p1 else simplify p1
  es3      = (stmts p1) ++ (Escape.check p1) ++ (Reachable.check p1) ++ (VarEvt.check p1)
