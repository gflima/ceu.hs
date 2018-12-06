module Ceu.Grammar.Check.Escape where

import Ceu.Grammar.Globals
import Ceu.Grammar.Stmt
import Debug.Trace

-- Checks `escape` without enclosing `trap`
-- Checks `trap` without nested `escape`
-- Returns all errors found

check :: (Stmt ann) -> Errors
check p = (checkTraps p) ++
          (errs_stmts_msg_map (map (\(s,n)->s) (getEscapes p)) "orphan `escape` statement")

neverEscapes p = (getEscapes p == [])

getEscapes :: (Stmt ann) -> [(Stmt ann,Int)]
getEscapes p = escs (-1) p where
  escs :: Int -> (Stmt ann) -> [(Stmt ann,Int)]
  escs n (Var _ _ p)     = (escs n p)
  escs n (Int _ _ p)     = (escs n p)
  escs n (If _ _ p1 p2)  = (escs n p1) ++ (escs n p2)
  escs n (Seq _ p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Loop _ p)      = (escs n p)
  escs n (Every _ _ p)   = (escs n p)
  escs n (Par _ p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Pause _ _ p)   = (escs n p)
  escs n (Fin _ p)       = (escs n p)
  escs n (Trap _ p)      = (escs (n+1) p)
  escs n s@(Escape _ k)
    | (n>=k) && (k>=0) = []
    | otherwise        = [(s, k-n)]
  escs _ _             = []

escapesAt1 p = (length $ filter (\(_,n) -> n==1) (getEscapes p)) >= 1

checkTraps :: (Stmt ann) -> Errors
checkTraps (Var _ _ p)     = (checkTraps p)
checkTraps (Int _ _ p)     = (checkTraps p)
checkTraps (If _ _ p1 p2)  = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Seq _ p1 p2)   = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Loop _ p)      = (checkTraps p)
checkTraps (Every _ _ p)   = (checkTraps p)
checkTraps (Par _ p1 p2)   = (checkTraps p1) ++ (checkTraps p2)
checkTraps (Pause _ _ p)   = (checkTraps p)
checkTraps (Fin _ p)       = (checkTraps p)
checkTraps s@(Trap _ p)    = res ++ (checkTraps p) where
  res =
    if (length $ filter (\(_,n) -> n==1) (getEscapes p)) == 0 then
      [err_stmt_msg s "missing `escape` statement"]
    else
      []
checkTraps _             = []

removeTrap :: (Stmt ann) -> (Stmt ann)
removeTrap (Trap _ p) = rT 0 p where
  rT :: Int -> (Stmt ann) -> (Stmt ann)
  rT n (Var z var p)      = Var z var (rT n p)
  rT n (Int z int p)      = Int z int (rT n p)
  rT n (If z exp p1 p2)   = If z exp (rT n p1) (rT n p2)
  rT n (Seq z p1 p2)      = Seq z (rT n p1) (rT n p2)
  rT n (Loop z p)         = Loop z (rT n p)
  rT n (Every z evt p)    = Every z evt (rT n p)
  rT n (Par z p1 p2)      = Par z (rT n p1) (rT n p2)
  rT n (Pause z var p)    = Pause z var (rT n p)
  rT n (Fin z p)          = Fin z (rT n p)
  rT n (Trap z p)         = Trap z (rT (n+1) p)
  rT n (Escape z k)
    | k < n = (Escape z k)
    | k > n = (Escape z (k-1))
    | otherwise = error "unexpected `escape` for `trap` being removed"
  rT n p                = p
