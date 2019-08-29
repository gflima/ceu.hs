module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = map_stmt (stmt,id,id) p

stmt :: Stmt -> Stmt

stmt (SSet z ini chk pat exp) = SMatch z ini chk exp [(SNop z,pat,SNop z)]
stmt (SIf  z exp p1 p2)       = SMatch z False False exp [
                                  (SNop z, EExp z (EVar z "_true"), p1),
                                  (SNop z, EAny z,                  p2)
                                 ]
stmt p = p
