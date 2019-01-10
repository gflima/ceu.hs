module Ceu.Grammar.Full.Compile.Trap where

import Debug.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Stmt

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux [] p) where
  aux :: [Maybe ID_Var] -> Stmt -> Stmt
  aux ids (Data' z tp vars cons abs p) = Data' z tp vars cons abs (aux ids p)
  aux ids (Var' z var tp fin p)   = Var' z var tp fin (aux ids p)
  aux ids (Inp' z id tp p)    = Inp' z id tp (aux ids p)
  aux ids (Out' z id tp p)    = Out' z id tp (aux ids p)
  aux ids (Evt' z id tp p)    = Evt' z id tp (aux ids p)
  aux ids (Func' z id tp p)   = Func' z id tp (aux ids p)
  aux ids (FuncI' z id tp imp p) = FuncI' z id tp (aux ids imp) (aux ids p)
  aux ids (If z exp p1 p2)    = If z exp (aux ids p1) (aux ids p2)
  aux ids (Seq z p1 p2)       = Seq z (aux ids p1) (aux ids p2)
  aux ids (Loop z p)          = Loop z (aux ids p)
  aux ids (Every z evt exp p) = Every z evt exp (aux ids p)
  aux ids (Par z p1 p2)       = Par z (aux ids p1) (aux ids p2)
  aux ids (And z p1 p2)       = And z (aux ids p1) (aux ids p2)
  aux ids (Or z p1 p2)        = Or z (aux ids p1) (aux ids p2)
  aux ids (Spawn z p)         = Spawn z (aux ids p)
  aux ids (Pause z evt p)     = Pause z evt (aux ids p)
  aux ids (Fin z a b c)       = Fin z (aux ids a) (aux ids b) (aux ids c)
  aux ids (Async z p)         = Async z (aux ids p)
  aux ids (Trap z var p)      = Trap' z (aux (var:ids) p)
  aux ids s@(Escape _ _ _)    = escape ids s 0
  aux ids p                   = p

escape :: [Maybe ID_Var] -> Stmt -> Int -> Stmt
escape (Nothing:_)     (Escape z Nothing  (Unit _)) _ = Escape' z 0
escape (Nothing:l)   s@(Escape z (Just _) (Unit _)) n = escape l s (n+1)
escape ((Just var):_)  (Escape z Nothing  exp)      _ = Seq z (Write z (LVar var) exp) (Escape' z 0)
escape ((Just var'):l) s@(Escape z (Just var) exp) n
  | var == var' = Seq z (Write z (LVar var) exp) (Escape' z n)
  | otherwise   = escape l s (n+1)
escape _ (Escape z _ _) _ = Escape' z (-1)

ins' :: Stmt -> Stmt
ins' p = (aux 0 p) where
  aux n (Var' z var tp Nothing p) = Var' z var tp Nothing (aux n p)
  aux n (Inp' z inp tp p)      = Inp' z inp tp (aux n p)
  aux n (Out' z out tp p)      = Out' z out tp (aux n p)
  aux n (Evt' z int tp p)      = Evt' z int tp (aux n p)
  aux n (Func' z cod tp p)     = Func' z cod tp (aux n p)
  aux n (If z exp p1 p2)       = If z exp (aux n p1) (aux n p2)
  aux n (Seq z p1 p2)          = Seq z (aux n p1) (aux n p2)
  aux n (Loop z p)             = Loop z (aux n p)
  aux n (Every z evt var p)    = Every z evt var (aux n p)
  aux n (Par' z p1 p2)         = Par' z (aux n p1) (aux n p2)
  aux n (Pause' z var p)       = Pause' z var (aux n p)
  aux n (Fin' z p)             = Fin' z (aux n p)
  aux n (Clean' z id p)        = Clean' z id (aux n p)
  aux n (Trap' z p)            = Trap' z (aux (n+1) p)
  aux n (Escape' z k)
    | k >= n                   = (Escape' z (k+1))
    | k <  n                   = (Escape' z k)
  aux n p                      = p
