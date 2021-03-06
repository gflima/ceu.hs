module Ceu.Grammar.Full.Compile.Spawn where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, toError)
import Ceu.Grammar.Full.Stmt

-- compile: Converts (spawn p1; ...) into (p1;Halt or ...)

compile :: Stmt -> (Errors, Stmt)
compile (Data' z id vars cons abs p) = (es, Data' z id vars cons abs p')
                                   where
                                     (es,p') = compile p
compile (Var' z id tp Nothing p) = (es, Var' z id tp Nothing p')
                                   where
                                     (es,p') = compile p
compile (Inp' z id tp p)         = (es, Inp' z id tp p')
                                   where
                                     (es,p') = compile p
compile (Out' z id tp p)         = (es, Out' z id tp p')
                                   where
                                     (es,p') = compile p
compile (Evt' z id tp p)         = (es, Evt' z id tp p')
                                   where
                                     (es,p') = compile p
compile (Func' z id tp p)        = (es, Func' z id tp p')
                                   where
                                     (es,p') = compile p
compile (FuncI' z id tp imp p)   = (esi++es, FuncI' z id tp imp' p')
                                   where
                                     (es, p')   = compile p
                                     (esi,imp') = compile imp
compile (If z exp p1 p2)         = (es1++es2, If z exp p1' p2')
                                   where
                                     (es1,p1') = compile p1
                                     (es2,p2') = compile p2
compile (Seq _ (Spawn z2 p1) p2) = compile (Or' z2 (Clean' z2 "Spawn" p1) p2)
compile (Seq z p1 p2)            = (es1++es2, Seq z p1' p2')
                                   where
                                     (es1,p1') = compile p1
                                     (es2,p2') = compile p2
compile (Loop z p)               = (es, Loop z p')
                                   where
                                     (es,p') = compile p
compile (Par z p1 p2)            = (es1++es2, Par z p1' p2')
                                   where
                                     (es1,p1') = compile p1
                                     (es2,p2') = compile p2
compile (Or z p1 p2)             = (es1++es2, Or z p1' p2')
                                   where
                                     (es1,p1') = compile p1
                                     (es2,p2') = compile p2
compile (Or' z p1 p2)            = (es1++es2, Or' z p1' p2')
                                   where
                                     (es1,p1') = compile p1
                                     (es2,p2') = compile p2
compile s@(Spawn z p)            = ([toError z "unexpected `spawn`"]++es, p')
                                   where
                                     (es,p') = compile (Seq z s (Nop z))
compile (Pause' z var p)         = (es, Pause' z var p')
                                   where
                                     (es,p') = compile p
compile (Trap' z p)              = (es, Trap' z p')
                                   where
                                     (es,p') = compile p
compile (Clean' z id p)          = (es, Clean' z id p')
                                   where
                                     (es,p') = compile p
compile p                      = ([], p)
