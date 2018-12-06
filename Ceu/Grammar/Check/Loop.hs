module Ceu.Grammar.Check.Loop where

import Ceu.Grammar.Stmt

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitExt/Every.
-- returns all `loop` that fail

check :: (Stmt ann) -> Bool

check (Loop _ body) = cL 0 body where
  cL n stmt = case stmt of
    AwaitExt _ _           -> True
    Every _ _ _            -> True
    Var _ _ p              -> cL n p
    Int _ _ p              -> cL n p
    If _ _ p q             -> cL n p && cL n q
    Seq _ s@(Escape _ _) q -> cL n s   -- q never executes
    Seq _ p q              -> cL n p || cL n q
    Loop _ p               -> cL n p
    Par _ p q              -> cL n p || cL n q
    Pause _ _ p            -> cL n p
    Trap _ p               -> cL (n+1) p
    Escape _ k             -> (k >= n)
    _                      -> False

check _ = error "checkLoop: expected Loop"
