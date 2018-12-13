module Ceu.Grammar.Full.Compile.Forever where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

-- compile: Converts AwaitFor into (AwaitExt "FOREVER")

compile :: (Stmt ann) -> (Errors, Stmt ann)
compile p = ([], aux p)
aux (Var' z id Nothing p) = Var' z id Nothing (aux p)
aux (Evt' z id b p)       = Evt' z id b (aux p)
aux (Out' z id b p)       = Out' z id b (aux p)
aux (If z exp p1 p2)      = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)         = Seq z (aux p1) (aux p2)
aux (Loop z p)            = Loop z (aux p)
aux (Par' z p1 p2)        = Par' z (aux p1) (aux p2)
aux (Pause' z var p)      = Pause' z var (aux p)
aux (Trap' z p)           = Trap' z (aux p)
aux (Clean' z id p)       = Clean' z id (aux p)
aux (AwaitFor z)          = AwaitExt z "FOREVER" Nothing
aux p                     = p
