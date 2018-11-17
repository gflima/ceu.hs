module Ceu.Grammar.Check.Escape where

import Ceu.Grammar

-- checks `escape` without enclosing `trap`
-- returns all errors found

check :: Stmt -> [(String,Stmt)]
check p = mapmsg "orphan `escape` statement" (escapes p)

escapes :: Stmt -> [Stmt]
escapes p = escs (-1) p where
  escs :: Int -> Stmt -> [Stmt]
  escs n (Var _ p)     = (escs n p)
  escs n (Int _ p)     = (escs n p)
  escs n (If _ p1 p2)  = (escs n p1) ++ (escs n p2)
  escs n (Seq p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Loop p)      = (escs (n+1) p)
  escs n (Every _ p)   = (escs n p)
  escs n (Par p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Pause _ p)   = (escs n p)
  escs n (Fin p)       = (escs n p)
  escs n (Trap p)      = (escs (n+1) p)
  escs n s@(Escape k)
    | (n >= k)         = []
    | otherwise        = [s]
  escs _ _             = []
