module Ceu.Grammar.Full.Compile.FuncS where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = aux p
aux :: Stmt -> Stmt
aux (FuncS z id tp imp)        = Seq z (Var z id tp)
                                       (Write z (LVar id)
                                        (Func z tp imp))
aux (If z exp p1 p2)           = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)              = Seq z (aux p1) (aux p2)
aux (Loop z p)                 = Loop z (aux p)
aux (Scope z p)                = Scope z (aux p)
aux p                          = p

