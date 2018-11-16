module Ceu.Grammar.Check.Escape where

import Ceu.Grammar

-- checks `escape` without enclosing `trap`
-- returns all errors found

check :: Stmt -> [Stmt]
check p = cE (-1) p where
  cE :: Int -> Stmt -> [Stmt]
  cE n (Var _ p)     = (cE n p)
  cE n (Int _ p)     = (cE n p)
  cE n (If _ p1 p2)  = (cE n p1) ++ (cE n p2)
  cE n (Seq p1 p2)   = (cE n p1) ++ (cE n p2)
  cE n (Loop p)      = (cE (n+1) p)
  cE n (Every _ p)   = (cE n p)
  cE n (Par p1 p2)   = (cE n p1) ++ (cE n p2)
  cE n (Pause _ p)   = (cE n p)
  cE n (Fin p)       = (cE n p)
  cE n (Trap p)      = (cE (n+1) p)
  cE n s@(Escape k)
    | (n >= k)       = []
    | otherwise      = [s]
  cE n p             = []
