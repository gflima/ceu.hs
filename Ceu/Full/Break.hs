module Ceu.Full.Break where

import Ceu.Full.Grammar

-- remove

remove :: Stmt -> Stmt
remove p = rB (-1) p where
  rB :: Int -> Stmt -> Stmt
  rB n (Var var Nothing p) = Var var Nothing (rB n p)
  rB n (Int int b p)       = Int int b (rB n p)
  rB n (If exp p1 p2)      = If exp (rB n p1) (rB n p2)
  rB n (Seq p1 p2)         = Seq (rB n p1) (rB n p2)
  rB n (Loop p)            = Trap' (Loop (rB (n+1) p))
  rB (-1) Break            = error "remBreak: `break` without `loop`"
  rB n Break               = Escape' n
  rB n (Every evt var p)   = Every evt var (rB n p)
  rB n (Par' p1 p2)        = Par' (rB n p1) (rB n p2)
  rB n (Pause' var p)      = Pause' var (rB n p)
  rB n (Fin' p)            = Fin' (rB n p)
  rB n (Trap' p)           = Trap' (rB (n+1) p)
  rB n (Clear' id p)       = Clear' id (rB n p)
  rB n p                   = p
