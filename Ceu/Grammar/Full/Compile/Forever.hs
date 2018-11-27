module Ceu.Grammar.Full.Compile.Forever where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

-- compile: Converts AwaitFor into (AwaitExt "FOREVER")

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux (Var id Nothing p) = Var id Nothing (aux p)
aux (Int id b p)       = Int id b (aux p)
aux (If exp p1 p2)     = If exp (aux p1) (aux p2)
aux (Seq p1 p2)        = Seq (aux p1) (aux p2)
aux (Loop p)           = Loop (aux p)
aux (Par' p1 p2)       = Par' (aux p1) (aux p2)
aux (Pause' var p)     = Pause' var (aux p)
aux (Trap' p)          = Trap' (aux p)
aux (Clean' id p)      = Clean' id (aux p)
aux AwaitFor           = AwaitExt "FOREVER" Nothing
aux p                  = p
