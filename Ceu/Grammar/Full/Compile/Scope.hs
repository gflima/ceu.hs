module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Stmt

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Data z tp vars cons abs)       = Data' z tp vars cons abs (Nop z)
aux (Var z var tp)                  = Var' z var tp (Nop z)
aux (If z exp p1 p2)                = If z exp (aux p1) (aux p2)
aux (Seq _ s@(Data z tp vars cons abs) p2) = Data' z tp vars cons abs (aux p2)
aux (Seq _ s@(Var z var tp) p2) = Var' z var tp (aux p2)
aux (Seq z p1 p2)                   = Seq z (aux p1) (aux p2)
aux (Loop z p)                      = Loop z (aux p)
aux (Scope _ p)                     = (aux p)
aux p                               = p
