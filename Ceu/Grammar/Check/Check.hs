module Ceu.Grammar.Check.Check where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Grammar
import Ceu.Grammar.Simplify
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Reachable as Reachable
import qualified Ceu.Grammar.Check.VarEvt    as VarEvt

getTights :: Stmt -> [String]
getTights p = errs_stmts_msg_map (aux' (-1) p) "invalid statement" where
  aux' _ s@(AwaitInt _) = [s]
  aux' _ s@(AwaitExt _) = [s]
  aux' n s@(Every _ p)  = [s] ++ aux' n p
  aux' n s@(Fin p)      = [s] ++ aux' n p
  aux' n s@(Loop p)     = aux' n p
  aux' n (Var _ p)      = aux' n p
  aux' n (Int _ p)      = aux' n p
  aux' n (If _ p q)     = aux' n p ++ aux' n q
  aux' n (Seq p q)      = aux' n p ++ aux' n q
  aux' n s@(Par p q)    = [s] ++ aux' n p ++ aux' n q
  aux' n s@(Pause _ p)  = [s] ++ aux' n p
  aux' n (Trap p)       = aux' (n+1) p
  aux' n s@(Escape k)
    | (n >= k)  = [s]
    | otherwise = [s]
  aux' _ _              = []

-- Checks if program is valid.
-- Returns all statements that fail.

stmts :: Stmt -> Errors
stmts stmt = case stmt of
  Var _ p       -> stmts p
  Int _ p       -> stmts p
  If _ p q      -> stmts p ++ stmts q
  Seq p q       -> stmts p ++ stmts q
  s@(Loop p)    -> stmts p ++ es where
                    es = if Loop.check s then
                           []
                         else
                           [err_stmt_msg s "unbounded `loop` execution"]
  s@(Every e p) -> stmts p ++ (aux "invalid statement in `every`" s p)
  s@(Par p q)   -> es ++ stmts p ++ stmts q where
                    es = if (Reachable.neverTerminates p) && (Reachable.neverTerminates q) then
                           []
                         else
                           [err_stmt_msg s "terminating trail"]
  Pause _ p     -> stmts p
  s@(Fin p)     -> stmts p ++ (aux "invalid statement in `finalize`" s p)
  Trap p        -> stmts p
  _             -> []
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
              (Var "_ret" (Seq (Trap p) (AwaitExt "FOREVER")))
  p2       = if not o_simp then p1 else simplify p1
  es3      = (stmts p2) ++ (Escape.check p2) ++ (Reachable.check p2) ++ (VarEvt.check p2)
