module Ceu.Grammar.Check.Escape where

import Ceu.Grammar.Globals
import Ceu.Grammar.Stmt
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
  escs n p = case getStmt' p of
    (Var _ p)    -> (escs n p)
    (Int _ p)    -> (escs n p)
    (If _ p1 p2) -> (escs n p1) ++ (escs n p2)
    (Seq p1 p2)  -> (escs n p1) ++ (escs n p2)
    (Loop p)     -> (escs n p)
    (Every _ p)  -> (escs n p)
    (Par p1 p2)  -> (escs n p1) ++ (escs n p2)
    (Pause _ p)  -> (escs n p)
    (Fin p)      -> (escs n p)
    (Trap p)     -> (escs (n+1) p)
    (Escape k)
      | (n>=k) && (k>=0) -> []
      | otherwise        -> [(p, k-n)]
    otherwise    -> []

escapesAt1 p = (length $ filter (\(_,n) -> n==1) (getEscapes p)) >= 1

checkTraps :: Stmt -> Errors
checkTraps s = case getStmt' s of
  (Var _ p)    -> (checkTraps p)
  (Int _ p)    -> (checkTraps p)
  (If _ p1 p2) -> (checkTraps p1) ++ (checkTraps p2)
  (Seq p1 p2)  -> (checkTraps p1) ++ (checkTraps p2)
  (Loop p)     -> (checkTraps p)
  (Every _ p)  -> (checkTraps p)
  (Par p1 p2)  -> (checkTraps p1) ++ (checkTraps p2)
  (Pause _ p)  -> (checkTraps p)
  (Fin p)      -> (checkTraps p)
  (Trap p)     -> res ++ (checkTraps p) where
    res =
      if (length $ filter (\(_,n) -> n==1) (getEscapes p)) == 0 then
        [err_stmt_msg s "missing `escape` statement"]
      else
        []
  otherwise    -> []

removeTrap :: Stmt -> Stmt
removeTrap p = case getStmt' p of
  (Trap p) -> rT 0 p where

    rT :: Int -> Stmt -> Stmt
    rT n p = newStmt $ rT' n (getStmt' p)

    rT' n s = case s of
      (Var var p)    -> Var var (rT n p)
      (Int int p)    -> Int int (rT n p)
      (If exp p1 p2) -> If exp (rT n p1) (rT n p2)
      (Seq p1 p2)    -> Seq (rT n p1) (rT n p2)
      (Loop p)       -> Loop (rT n p)
      (Every evt p)  -> Every evt (rT n p)
      (Par p1 p2)    -> Par (rT n p1) (rT n p2)
      (Pause var p)  -> Pause var (rT n p)
      (Fin p)        -> Fin (rT n p)
      (Trap p)       -> Trap (rT (n+1) p)
      (Escape k)
        | k < n      -> (Escape k)
        | k > n      -> (Escape (k-1))
        | otherwise  -> error "unexpected `escape` for `trap` being removed"
      otherwise      -> s

  otherwise -> error "removeTrap: expected Trap"
