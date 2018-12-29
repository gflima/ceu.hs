module Ceu.Grammar.Check where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann(..), errs_anns_msg_map)
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Stmt     (Stmt(..), getAnn)
import Ceu.Grammar.Simplify (simplify)
import qualified Ceu.Grammar.TypeSys as TypeSys

-------------------------------------------------------------------------------

type Options = (Bool,Bool,Bool)

compile :: (Ann a) => Options -> (Stmt a) -> (Errors, Stmt a)
compile (o_simp,o_encl,o_prel) p = (es3,p3) where
    -- TODO: o_prel
  p1   = if not o_encl then p else
          (Var z "_ret" (Type1 "Int") (Seq z (Trap z p) (Halt z)))
  (es2,p2) = TypeSys.go p1
  p3   = if not o_simp then p2 else simplify p2
  es3  = escs ++ (stmts p1) ++ es2
  z    = getAnn p
  escs = errs_anns_msg_map (map (\(s,n)->getAnn s) (getEscapes p1)) "orphan `escape` statement"


stmts :: (Ann a) => (Stmt a) -> Errors
stmts stmt = case stmt of
  Var _ _ _ p     -> stmts p
  Inp _ _ p       -> stmts p
  Out _ _ p       -> stmts p
  Evt _ _ p       -> stmts p
  Func _ _ _ p    -> stmts p
  If _ _ p q      -> stmts p ++ stmts q
  Seq _ p q       -> stmts p ++ stmts q ++ es where
                     es = if (maybeTerminates p) then [] else
                            [toError (getAnn q) "unreachable statement"]
  s@(Loop z p)    -> stmts p ++ es1 ++ es2 where
                     es1 = if boundedLoop s then [] else
                            [toError z "unbounded `loop` execution"]
                     es2 = if maybeTerminates p then [] else
                            [toError z "`loop` never iterates"]
  Every z e p     -> stmts p ++ (aux "invalid statement in `every`" z p)
  Par z p q       -> es ++ stmts p ++ stmts q where
                     es = if (neverTerminates p) && (neverTerminates q) then
                             []
                          else
                             [toError z "terminating trail"]
  Pause _ _ p     -> stmts p
  Fin z p         -> stmts p ++ (aux "invalid statement in `finalize`" z p)
  Trap z p        -> es1 ++ es2 ++ stmts p where
                     es1 = if neverTerminates p then [] else
                             [toError z "terminating `trap` body"]
                     es2 = if escapesAt0 p then [] else
                             [toError z "missing `escape` statement"]
  _               -> []
  where
    aux msg z p =
      let ret = getComplexs p in
        if (ret == []) then
          []
        else
          [toError z msg] ++ ret

-------------------------------------------------------------------------------

getComplexs :: (Ann a) => (Stmt a) -> [String]
getComplexs p = errs_anns_msg_map (aux' (-1) p) "invalid statement" where
  aux' _ (AwaitEvt z _) = [z]
  aux' _ (AwaitInp z _) = [z]
  aux' n (Every z _ p)  = [z] ++ aux' n p
  aux' n (Fin z p)      = [z] ++ aux' n p
  aux' n (Loop _ p)     = aux' n p
  aux' n (Var _ _ _ p)  = aux' n p
  aux' n (Inp _ _ p)    = aux' n p
  aux' n (Out _ _ p)    = aux' n p
  aux' n (Evt _ _ p)    = aux' n p
  aux' n (Func _ _ _ p) = aux' n p
  aux' n (If _ _ p q)   = aux' n p ++ aux' n q
  aux' n (Seq _ p q)    = aux' n p ++ aux' n q
  aux' n (Par z p q)    = [z] ++ aux' n p ++ aux' n q
  aux' n (Pause z _ p)  = [z] ++ aux' n p
  aux' n (Trap _ p)     = aux' (n+1) p
  aux' n (Escape z k)
    | (n >= k)          = [z]
    | otherwise         = [z]
  aux' _ (Halt z)       = [z]
  aux' _ _              = []

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitInp/Every.
-- returns all `loop` that fail

boundedLoop :: (Stmt a) -> Bool
boundedLoop (Loop _ body) = aux 0 body where
  aux n stmt = case stmt of
    AwaitInp _ _           -> True
    Every _ _ _            -> True
    Var _ _ _ p            -> aux n p
    Inp _ _ p              -> aux n p
    Out _ _ p              -> aux n p
    Evt _ _ p              -> aux n p
    Func _ _ _ p           -> aux n p
    If _ _ p q             -> aux n p && aux n q
    Seq _ s@(Escape _ _) q -> aux n s   -- q never executes
    Seq _ p q              -> aux n p || aux n q
    Loop _ p               -> aux n p
    Par _ p q              -> aux n p || aux n q
    Pause _ _ p            -> aux n p
    Trap _ p               -> aux (n+1) p
    Escape _ k             -> (k >= n)
    Halt _                 -> True
    _                      -> False

-------------------------------------------------------------------------------

neverEscapes p = (getEscapes p == [])

escapesAt0 p = (length $ filter (\(_,n) -> n==0) (getEscapes p)) >= 1

getEscapes :: (Stmt a) -> [(Stmt a,Int)]
getEscapes p = escs 0 p where
  escs :: Int -> (Stmt a) -> [(Stmt a,Int)]
  escs n (Var _ _ _ p)    = (escs n p)
  escs n (Inp _ _ p)      = (escs n p)
  escs n (Out _ _ p)      = (escs n p)
  escs n (Evt _ _ p)      = (escs n p)
  escs n (Func _ _ _ p)   = (escs n p)
  escs n (If _ _ p1 p2)   = (escs n p1) ++ (escs n p2)
  escs n (Seq _ p1 p2)    = (escs n p1) ++ (escs n p2)
  escs n (Loop _ p)       = (escs n p)
  escs n (Every _ _ p)    = (escs n p)
  escs n (Par _ p1 p2)    = (escs n p1) ++ (escs n p2)
  escs n (Pause _ _ p)    = (escs n p)
  escs n (Fin _ p)        = (escs n p)
  escs n (Trap _ p)       = (escs (n+1) p)
  escs n s@(Escape _ k)
    | n>k && k/=(-1)      = []    -- 3 vs (escape 2)
    | otherwise           = [(s, k-n)]
  escs _ _                = []

removeTrap :: (Stmt a) -> (Stmt a)
removeTrap (Trap _ p) = rT 0 p where
  rT :: Int -> (Stmt a) -> (Stmt a)
  rT n (Var z id tp p)       = Var z id tp (rT n p)
  rT n (Inp z id p)          = Inp z id (rT n p)
  rT n (Out z id p)          = Out z id (rT n p)
  rT n (Evt z id p)          = Evt z id (rT n p)
  rT n (Func z id tp p)      = Func z id tp (rT n p)
  rT n (If z exp p1 p2)      = If z exp (rT n p1) (rT n p2)
  rT n (Seq z p1 p2)         = Seq z (rT n p1) (rT n p2)
  rT n (Loop z p)            = Loop z (rT n p)
  rT n (Every z evt p)       = Every z evt (rT n p)
  rT n (Par z p1 p2)         = Par z (rT n p1) (rT n p2)
  rT n (Pause z var p)       = Pause z var (rT n p)
  rT n (Fin z p)             = Fin z (rT n p)
  rT n (Trap z p)            = Trap z (rT (n+1) p)
  rT n (Escape z k)
    | k < n = (Escape z k)
    | k > n = (Escape z (k-1))
    | otherwise = error "unexpected `escape` for `trap` being removed"
  rT n p                     = p

-------------------------------------------------------------------------------

neverTerminates :: (Stmt a) -> Bool
neverTerminates (Var _ _ _ p)    = neverTerminates p
neverTerminates (Inp _ _ p)      = neverTerminates p
neverTerminates (Out _ _ p)      = neverTerminates p
neverTerminates (Evt _ _ p)      = neverTerminates p
neverTerminates (Func _ _ _ p)   = neverTerminates p
neverTerminates (Halt _)         = True
neverTerminates (If _ _ p1 p2)   = neverTerminates p1 && neverTerminates p2
neverTerminates (Seq _ p1 p2)    = neverTerminates p1 || neverTerminates p2
neverTerminates (Loop _ p)       = True
neverTerminates (Every _ _ p)    = True
neverTerminates (Par _ p1 p2)    = True
neverTerminates (Pause _ _ p)    = neverTerminates p
neverTerminates (Fin _ p)        = True
neverTerminates (Trap _ p)       = not $ escapesAt0 p
neverTerminates (Escape _ _)     = True
neverTerminates _                = False

maybeTerminates = not . neverTerminates

alwaysTerminates :: (Stmt a) -> Bool
alwaysTerminates (Var _ _ _ p)    = alwaysTerminates p
alwaysTerminates (Inp _ _ p)      = alwaysTerminates p
alwaysTerminates (Out _ _ p)      = alwaysTerminates p
alwaysTerminates (Evt _ _ p)      = alwaysTerminates p
alwaysTerminates (Func _ _ _ p)   = alwaysTerminates p
alwaysTerminates (Halt _)         = False
alwaysTerminates (If _ _ p1 p2)   = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Seq _ p1 p2)    = alwaysTerminates p1 && alwaysTerminates p2
alwaysTerminates (Loop _ p)       = False
alwaysTerminates (Every _ _ p)    = False
alwaysTerminates (Par _ p1 p2)    = False
alwaysTerminates (Pause _ _ p)    = alwaysTerminates p
alwaysTerminates (Fin _ p)        = False
alwaysTerminates (Trap _ p)       = escapesAt0 p
alwaysTerminates (Escape _ _)     = False
alwaysTerminates _                = True

-------------------------------------------------------------------------------

alwaysInstantaneous :: (Stmt a) -> Bool
alwaysInstantaneous p = aux p where
  aux (Var _ _ _ p)    = aux p
  aux (Inp _ _ p)      = aux p
  aux (Out _ _ p)      = aux p
  aux (Evt _ _ p)      = aux p
  aux (Func _ _ _ p)   = aux p
  aux (AwaitInp _ _)   = False
  aux (AwaitEvt _ _)   = False
  aux (If _ _ p1 p2)   = aux p1 && aux p2
  aux (Seq _ p1 p2)    = aux p1 && aux p2
  aux (Loop _ p)       = False
  aux (Every _ _ _)    = False
  aux (Par _ _ _)      = False
  aux (Pause _ _ p)    = aux p
  aux (Fin _ p)        = False
  aux (Trap _ p)       = aux p
  aux (Halt _)         = False
  aux _                = True

{-
neverInstantaneous :: (Stmt a) -> Bool
neverInstantaneous p = aux p where
  aux (Var _ _ _ p)  = aux p
  aux (Inp _ _ p)    = aux p
  aux (Out _ _ p)    = aux p
  aux (Evt _ _ p)      = aux p
  aux (Func _ _ _ p)   = aux p
  aux (AwaitInp _ _)   = True
  aux (If _ _ p1 p2)   = aux p1 && aux p2
  aux (Seq _ p1 p2)    = aux p1 || aux p2
  aux (Loop _ p)       = True
  aux (Every _ _ _)    = True
  aux (Par _ _ _)      = True
  aux (Pause _ _ p)    = aux p
  aux (Fin _ p)        = True
  aux (Trap _ p)       = aux p
  aux (Halt _)         = True
  aux _                = False
-}
