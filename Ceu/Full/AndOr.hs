module Ceu.Full.AndOr where

import Ceu.Full.Grammar

-- remove

remove :: Stmt -> Stmt
remove (Var var Nothing p) = Var var Nothing (remove p)
remove (Int int b p)       = Int int b (remove p)
remove (If exp p1 p2)      = If exp (remove p1) (remove p2)
remove (Seq p1 p2)         = Seq (remove p1) (remove p2)
remove (Loop p)            = Loop (remove p)
remove (And p1 p2)         = Par' (remove p1) (remove p2)
remove (Or p1 p2)          = Trap' (Par' (Seq (remove p1) (Escape' 0)) (Seq (remove p2) (Escape' 0)))
remove (Pause' var p)      = Pause' var (remove p)
remove (Trap' p)           = Trap' (remove p)
remove p                   = p
