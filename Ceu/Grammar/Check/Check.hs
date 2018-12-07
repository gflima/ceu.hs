module Ceu.Grammar.Check.Check where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Stmt
import Ceu.Grammar.Simplify
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Reachable as Reachable
import qualified Ceu.Grammar.Check.VarEvt    as VarEvt

getComplexs :: (Stmt ann) -> [String]
getComplexs p = errs_stmts_msg_map (aux' (-1) p) "invalid statement" where
  aux' _ s@(AwaitInt _ _) = [s]
  aux' _ s@(AwaitExt _ _) = [s]
  aux' n s@(Every _ _ p)  = [s] ++ aux' n p
  aux' n s@(Fin _ p)      = [s] ++ aux' n p
  aux' n s@(Loop _ p)     = aux' n p
  aux' n (Var _ _ p)      = aux' n p
  aux' n (Int _ _ p)      = aux' n p
  aux' n (If _ _ p q)     = aux' n p ++ aux' n q
  aux' n (Seq _ p q)      = aux' n p ++ aux' n q
  aux' n s@(Par _ p q)    = [s] ++ aux' n p ++ aux' n q
  aux' n s@(Pause _ _ p)  = [s] ++ aux' n p
  aux' n (Trap _ p)       = aux' (n+1) p
  aux' n s@(Escape _ k)
    | (n >= k)            = [s]
    | otherwise           = [s]
  aux' _ _                = []

-- Checks if program is valid.
-- Returns all statements that fail.

stmts :: (Stmt ann) -> Errors
stmts stmt = case stmt of
  Var _ _ p       -> stmts p
  Int _ _ p       -> stmts p
  If _ _ p q      -> stmts p ++ stmts q
  Seq _ p q       -> stmts p ++ stmts q
  s@(Loop _ p)    -> stmts p ++ es where
                     es = if Loop.check s then
                             []
                          else
                             [err_stmt_msg s "unbounded `loop` execution"]
  s@(Every _ e p) -> stmts p ++ (aux "invalid statement in `every`" s p)
  s@(Par _ p q)   -> es ++ stmts p ++ stmts q where
                     es = if (Reachable.neverTerminates p) && (Reachable.neverTerminates q) then
                             []
                          else
                             [err_stmt_msg s "terminating trail"]
  Pause _ _ p     -> stmts p
  s@(Fin _ p)     -> stmts p ++ (aux "invalid statement in `finalize`" s p)
  Trap _ p        -> stmts p
  _               -> []
  where
    aux msg s p =
      let ret = getComplexs p in
        if (ret == []) then
          []
        else
          [err_stmt_msg s msg] ++ ret

type Options = (Bool,Bool)

compile :: (Eq ann) => Options -> (Stmt ann) -> (Errors, Stmt ann)
compile (o_simp,o_encl) p = (es3,p2) where
  p1  = if not o_encl then p else
          (Var z "_ret" (Seq z (Trap z p) (AwaitExt z "FOREVER")))
  p2  = if not o_simp then p1 else simplify p1
  es3 = (stmts p1) ++ (Escape.check p1) ++ (Reachable.check p1) ++ (VarEvt.check p1)
  z   = getAnn p
