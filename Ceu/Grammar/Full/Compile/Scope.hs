module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Data z tp vars cons abs)       = Data' z tp vars cons abs (Nop z)
stmt (Var z var tp)                  = Var' z var tp (Nop z)
stmt (Write z loc exp)               = Write z loc (expr exp)
stmt (CallS z exp1 exp2)             = CallS z (expr exp1) (expr exp2)
stmt (If z exp p1 p2)                = If z (expr exp) (stmt p1) (stmt p2)
stmt (Seq _ s@(Data z tp vars cons abs) p2) = Data' z tp vars cons abs (stmt p2)
stmt (Seq _ s@(Var z var tp) p2)     = Var' z var tp (stmt p2)
stmt (Seq z p1 p2)                   = Seq z (stmt p1) (stmt p2)
stmt (Loop z p)                      = Loop z (stmt p)
stmt (Scope _ p)                     = (stmt p)
stmt (Ret z exp)                     = Ret z (expr exp)
stmt p                               = p

expr :: Exp -> Exp
expr (Call z e1 e2)                 = Call z (expr e1) (expr e2)
expr (Func z tp p)                  = Func z tp (stmt p)
expr e                              = e

