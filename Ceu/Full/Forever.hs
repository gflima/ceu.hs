module Ceu.Full.Forever where

import Ceu.Full.Grammar

-- remove: Converts AwaitFor into (AwaitExt "FOREVER")

remove :: Stmt -> Stmt
remove (Var id Nothing p) = Var id Nothing (remove p)
remove (Int id b p)       = Int id b (remove p)
remove (If exp p1 p2)     = If exp (remove p1) (remove p2)
remove (Seq p1 p2)        = Seq (remove p1) (remove p2)
remove (Loop p)           = Loop (remove p)
remove (Par' p1 p2)       = Par' (remove p1) (remove p2)
remove (Pause' var p)     = Pause' var (remove p)
remove (Trap' p)          = Trap' (remove p)
remove (Clear' id p)      = Clear' id (remove p)
remove AwaitFor           = AwaitExt "FOREVER" Nothing
remove p                  = p


