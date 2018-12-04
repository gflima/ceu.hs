module Ceu.Grammar.Check.Loop where

import Ceu.Grammar.Stmt

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitExt/Every.
-- returns all `loop` that fail

check :: Stmt -> Bool
check s = case getStmt' s of
  Loop body -> cL 0 (getStmt' body) where
    cL n stmt = case stmt of
      AwaitExt _       -> True
      Every _ _        -> True
      Var _ p          -> cL n (getStmt' p)
      Int _ p          -> cL n (getStmt' p)
      If _ p q         -> cL n (getStmt' p) && cL n (getStmt' q)
      Seq p q          -> case getStmt' p of
                            Escape k  -> cL n (Escape k) -- q never executes
                            otherwise -> cL n (getStmt' p) || cL n (getStmt' q)
      Loop p           -> cL n (getStmt' p)
      Par p q          -> cL n (getStmt' p) || cL n (getStmt' q)
      Pause _ p        -> cL n (getStmt' p)
      Trap p           -> cL (n+1) (getStmt' p)
      Escape k         -> (k >= n)
      _                -> False
  otherwise -> error "checkLoop: expected Loop"
