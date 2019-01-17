module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Stmt

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Data z id vars cons abs)  = Data z id vars cons abs
aux (Var z id tp)              = Var z id tp
aux (If z exp p1 p2)           = If z exp (aux p1) (aux p2)
aux (Seq z1 (Seq z2 p1 p2) p3) = aux $ Seq z1 p1 (Seq z2 p2 p3)
aux (Seq z p1 p2)              = Seq z (aux p1) (aux p2)
aux (Loop z p)                 = Loop z (aux p)
aux (Scope z p)                = Scope z (aux p)
aux p                          = p
