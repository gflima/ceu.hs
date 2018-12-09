module Ceu.Grammar.Check where

import Debug.Trace

import Ceu.Grammar.Globals  (Errors)
import Ceu.Grammar.Stmt     (Stmt(..), getAnn, err_stmt_msg, errs_stmts_msg_map)
import Ceu.Grammar.Simplify (simplify)
import qualified Ceu.Grammar.VarEvt as VarEvt

-------------------------------------------------------------------------------

type Options = (Bool,Bool)

compile :: Eq ann => Options -> (Stmt ann) -> (Errors, Stmt ann)
compile (o_simp,o_encl) p = (es3,p2) where
  p1   = if not o_encl then p else
          (Var z "_ret" (Seq z (Trap z p) (AwaitExt z "FOREVER")))
  p2   = if not o_simp then p1 else simplify p1
  es3  = escs ++ (stmts p1) ++ (VarEvt.check p1)
  z    = getAnn p
  escs = errs_stmts_msg_map (map (\(s,n)->s) (getEscapes p1)) "orphan `escape` statement"


stmts :: (Stmt ann) -> Errors
stmts stmt = case stmt of
  Var _ _ p       -> stmts p
  Int _ _ p       -> stmts p
  If _ _ p q      -> stmts p ++ stmts q
  Seq _ p q       -> stmts p ++ stmts q ++ es where
                     es = if (maybeTerminates p) then [] else
                            [err_stmt_msg q "unreachable statement"]
  s@(Loop _ p)    -> stmts p ++ es1 ++ es2 where
                     es1 = if boundedLoop s then [] else
                            [err_stmt_msg s "unbounded `loop` execution"]
                     es2 = if maybeTerminates p then [] else
                            [err_stmt_msg s "`loop` never iterates"]
  s@(Every _ e p) -> stmts p ++ (aux "invalid statement in `every`" s p)
  s@(Par _ p q)   -> es ++ stmts p ++ stmts q where
                     es = if (neverTerminates p) && (neverTerminates q) then
                             []
                          else
                             [err_stmt_msg s "terminating trail"]
  Pause _ _ p     -> stmts p
  s@(Fin _ p)     -> stmts p ++ (aux "invalid statement in `finalize`" s p)
  s@(Trap _ p)    -> stmts p ++ es1 ++ es2 where
                     es1 = if neverTerminates p then [] else
                             [err_stmt_msg s "terminating `trap` body"]
                     es2 = if escapesAt0 p then [] else
                             [err_stmt_msg s "missing `escape` statement"]
  _               -> []
  where
    aux msg s p =
      let ret = getComplexs p in
        if (ret == []) then
          []
        else
          [err_stmt_msg s msg] ++ ret

-------------------------------------------------------------------------------

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

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitExt/Every.
-- returns all `loop` that fail

boundedLoop :: (Stmt ann) -> Bool
boundedLoop (Loop _ body) = cL 0 body where
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

-------------------------------------------------------------------------------

neverEscapes p = (getEscapes p == [])

escapesAt0 p = (length $ filter (\(_,n) -> n==0) (getEscapes p)) >= 1

getEscapes :: (Stmt ann) -> [(Stmt ann,Int)]
getEscapes p = escs 0 p where
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
    | n>k && k/=(-1)     = []    -- 3 vs (escape 2)
    | otherwise          = [(s, k-n)]
  escs _ _               = []

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

-------------------------------------------------------------------------------

neverTerminates :: (Stmt ann) -> Bool
neverTerminates (Var _ _ p)            = neverTerminates p
neverTerminates (Int _ _ p)            = neverTerminates p
neverTerminates (AwaitExt _ "FOREVER") = True
neverTerminates (If _ _ p1 p2)         = neverTerminates p1 && neverTerminates p2
neverTerminates (Seq _ p1 p2)          = neverTerminates p1 || neverTerminates p2
neverTerminates (Loop _ p)             = True
neverTerminates (Every _ _ p)          = True
neverTerminates (Par _ p1 p2)          = True
neverTerminates (Pause _ _ p)          = neverTerminates p
neverTerminates (Fin _ p)              = True
neverTerminates (Trap _ p)             = not $ escapesAt0 p
neverTerminates (Escape _ _)           = True
neverTerminates _                      = False

maybeTerminates = not . neverTerminates

alwaysTerminates :: (Stmt ann) -> Bool
alwaysTerminates (Var _ _ p)            = alwaysTerminates p
alwaysTerminates (Int _ _ p)            = alwaysTerminates p
alwaysTerminates (AwaitExt _ "FOREVER") = False
alwaysTerminates (If _ _ p1 p2)         = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Seq _ p1 p2)          = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Loop _ p)             = False
alwaysTerminates (Every _ _ p)          = False
alwaysTerminates (Par _ p1 p2)          = False
alwaysTerminates (Pause _ _ p)          = alwaysTerminates p
alwaysTerminates (Fin _ p)              = False
alwaysTerminates (Trap _ p)             = escapesAt0 p
alwaysTerminates (Escape _ _)           = False
alwaysTerminates _                      = True

-------------------------------------------------------------------------------

alwaysInstantaneous :: (Stmt ann) -> Bool
alwaysInstantaneous p = aux p where
  aux (Var _ _ p)    = aux p
  aux (Int _ _ p)    = aux p
  aux (AwaitExt _ _) = False
  aux (AwaitInt _ _) = False
  aux (If _ _ p1 p2) = aux p1 && aux p2
  aux (Seq _ p1 p2)  = aux p1 && aux p2
  aux (Loop _ p)     = False
  aux (Every _ _ _)  = False
  aux (Par _ _ _)    = False
  aux (Pause _ _ p)  = aux p
  aux (Fin _ p)      = False
  aux (Trap _ p)     = aux p
  aux _              = True

{-
neverInstantaneous :: (Stmt ann) -> Bool
neverInstantaneous p = aux p where
  aux (Var _ _ p)    = aux p
  aux (Int _ _ p)    = aux p
  aux (AwaitExt _ _) = True
  aux (If _ _ p1 p2) = aux p1 && aux p2
  aux (Seq _ p1 p2)  = aux p1 || aux p2
  aux (Loop _ p)     = True
  aux (Every _ _ _)  = True
  aux (Par _ _ _)    = True
  aux (Pause _ _ p)  = aux p
  aux (Fin _ p)      = True
  aux (Trap _ p)     = aux p
  aux _              = False
-}
