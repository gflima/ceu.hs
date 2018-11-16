module Ceu.Grammar.Check.Loop where

import Ceu.Grammar

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitExt/Every.
-- returns all `loop` that fail

check :: Stmt -> Bool

check (Loop body) = cL 0 body where
  cL n stmt = case stmt of
    AwaitExt _       -> True
    Every _ _        -> True
    Var _ p          -> cL n p
    Int _ p          -> cL n p
    If _ p q         -> cL n p && cL n q
    Seq (Escape k) q -> cL n (Escape k)   -- q never executes
    Seq p q          -> cL n p || cL n q
    Loop p           -> cL n p
    Par p q          -> cL n p && cL n q
    Pause _ p        -> cL n p
    Trap p           -> cL (n+1) p
    Escape k        -> (k >= n)
    _                -> False

check _ = error "checkLoop: expected Loop"
