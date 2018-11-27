module Ceu.Grammar.Full.Compile.Spawn where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

-- compile: Converts (spawn p1; ...) into (p1;AwaitFor or ...)

compile :: Stmt -> (Errors, Stmt)
compile (Var id Nothing p)  = (es, Var id Nothing p')
                                where
                                  (es,p') = compile p
compile (Int id b p)        = (es, Int id b p')
                                where
                                  (es,p') = compile p
compile (If exp p1 p2)      = (es1++es2, If exp p1' p2')
                                where
                                  (es1,p1') = compile p1
                                  (es2,p2') = compile p2
compile (Seq (Spawn p1) p2) = compile (Or' (Clean' "Spawn" p1) p2)
compile (Seq p1 p2)         = (es1++es2, Seq p1' p2')
                                where
                                  (es1,p1') = compile p1
                                  (es2,p2') = compile p2
compile (Loop p)            = (es, Loop p')
                                where
                                  (es,p') = compile p
compile (Par p1 p2)         = (es1++es2, Par p1' p2')
                                where
                                  (es1,p1') = compile p1
                                  (es2,p2') = compile p2
compile (Or p1 p2)          = (es1++es2, Or p1' p2')
                                where
                                  (es1,p1') = compile p1
                                  (es2,p2') = compile p2
compile (Or' p1 p2)         = (es1++es2, Or' p1' p2')
                                where
                                  (es1,p1') = compile p1
                                  (es2,p2') = compile p2
compile s@(Spawn p)         = ([err_stmt_msg s "unexpected `spawn`"]++es, p')
                                where
                                  (es,p') = compile (Seq s Nop)
compile (Pause' var p)      = (es, Pause' var p')
                                where
                                  (es,p') = compile p
compile (Trap' p)           = (es, Trap' p')
                                where
                                  (es,p') = compile p
compile (Clean' id p)       = (es, Clean' id p')
                                where
                                  (es,p') = compile p
compile p                   = ([], p)
