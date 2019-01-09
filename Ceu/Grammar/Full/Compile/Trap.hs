module Ceu.Grammar.Full.Compile.Trap where

import Debug.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Stmt

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux [] p) where
  aux :: [Maybe ID_Var] -> Stmt -> Stmt
  aux vars (Var' z var tp fin p) = Var' z var tp fin (aux vars p)
  aux vars (Inp' z id tp p)    = Inp' z id tp (aux vars p)
  aux vars (Out' z id tp p)    = Out' z id tp (aux vars p)
  aux vars (Evt' z id tp p)    = Evt' z id tp (aux vars p)
  aux vars (Func' z id tp p)   = Func' z id tp (aux vars p)
  aux vars (FuncI' z id tp imp p) = FuncI' z id tp (fmap (aux vars) imp) (aux vars p)
  aux vars (If z exp p1 p2)    = If z exp (aux vars p1) (aux vars p2)
  aux vars (Seq z p1 p2)       = Seq z (aux vars p1) (aux vars p2)
  aux vars (Loop z p)          = Loop z (aux vars p)
  aux vars (Every z evt exp p) = Every z evt exp (aux vars p)
  aux vars (Par z p1 p2)       = Par z (aux vars p1) (aux vars p2)
  aux vars (And z p1 p2)       = And z (aux vars p1) (aux vars p2)
  aux vars (Or z p1 p2)        = Or z (aux vars p1) (aux vars p2)
  aux vars (Spawn z p)         = Spawn z (aux vars p)
  aux vars (Pause z evt p)     = Pause z evt (aux vars p)
  aux vars (Fin z a b c)       = Fin z (aux vars a) (aux vars b) (aux vars c)
  aux vars (Async z p)         = Async z (aux vars p)
  aux vars (Trap z var p)      = Trap' z (aux (var:vars) p)
  aux vars s@(Escape _ _ _)    = escape vars s 0
  aux vars p                   = p

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
