module Ceu.Grammar.Check.Escape where

import Ceu.Globals
import Ceu.Grammar
import Debug.Trace

-- Checks `escape` without enclosing `trap`
-- Checks `trap` without nested `escape`
-- Returns all errors found

check :: Stmt -> Errors
check p = (checkTraps p) ++
          (errs_stmts_msg_map (map (\(s,n)->s) (getEscapes p)) "orphan `escape` statement")

neverEscapes p = (getEscapes p == [])

getEscapes :: Stmt -> [(Stmt,Int)]
getEscapes p = escs (-1) p where
  escs :: Int -> Stmt -> [(Stmt,Int)]
  escs n (Var _ p)     = (escs n p)
  escs n (Int _ p)     = (escs n p)
  escs n (If _ p1 p2)  = (escs n p1) ++ (escs n p2)
  escs n (Seq p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Loop p)      = (escs n p)
  escs n (Every _ p)   = (escs n p)
  escs n (Par p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Pause _ p)   = (escs n p)
  escs n (Fin p)       = (escs n p)
  escs n (Trap p)      = (escs (n+1) p)
  escs n s@(Escape k)
    | (n >= k)         = []
    | otherwise        = [(s, k-n)]
  escs _ _             = []

escapesAt1 p = (length $ filter (\(_,n) -> n==1) (getEscapes p)) >= 1

checkTraps :: Stmt -> Errors
checkTraps (Var _ p)     = (checkTraps p)
checkTraps (Int _ p)     = (checkTraps p)
checkTraps (If _ p1 p2)  = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Seq p1 p2)   = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Loop p)      = (checkTraps p)
checkTraps (Every _ p)   = (checkTraps p)
checkTraps (Par p1 p2)   = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Pause _ p)   = (checkTraps p)
checkTraps (Fin p)       = (checkTraps p)
checkTraps s@(Trap p)    = res ++ (checkTraps p) where
  res =
    if (length $ filter (\(_,n) -> n==1) (getEscapes p)) == 0 then
      [err_stmt_msg s "missing `escape` statement"]
    else
      []
checkTraps _             = []

removeTrap :: Stmt -> Stmt
removeTrap (Trap p) = rT 0 p where
  rT :: Int -> Stmt -> Stmt
  rT n (Var var p)      = Var var (rT n p)
  rT n (Int int p)      = Int int (rT n p)
  rT n (If exp p1 p2)   = If exp (rT n p1) (rT n p2)
  rT n (Seq p1 p2)      = Seq (rT n p1) (rT n p2)
  rT n (Loop p)         = Loop (rT n p)
  rT n (Every evt p)    = Every evt (rT n p)
  rT n (Par p1 p2)      = Par (rT n p1) (rT n p2)
  rT n (Pause var p)    = Pause var (rT n p)
  rT n (Fin p)          = Fin (rT n p)
  rT n (Trap p)         = Trap (rT (n+1) p)
  rT n (Escape k)
    | k < n = (Escape k)
    | k > n = (Escape (k-1))
    | otherwise = error "unexpected `escape` for `trap` being removed"
  rT n p                = p
