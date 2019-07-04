module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Inst   z cls tp imp)        = Inst   z cls tp (stmt imp)
stmt (Match' z chk exp cses)      = Match' z chk (expr exp)
                                      (map (\(pt,st) -> (expr pt, stmt st)) cses)
stmt (CallS  z exp)               = CallS  z (expr exp)
--stmt (Seq    z (Match' z' False exp ((pat1,st1):l)) p) = stmt $ Match' z' False exp ((pat1,(Seq z st1 p)):l)
stmt (Seq    z (Seq z' p1 p2) p3) = stmt $ Seq z p1 (Seq z' p2 p3)
stmt (Seq    z p1 p2)             = Seq    z (stmt p1) (stmt p2)
stmt (Loop   z p)                 = Loop   z (stmt p)
stmt (Scope  z p)                 = Scope  z (stmt p)
stmt (Ret    z exp)               = Ret  z (expr exp)
stmt p                            = p

expr :: Exp -> Exp
expr (ETuple z es)              = ETuple z (map expr es)
expr (ECall  z e1 e2)           = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)            = EFunc  z tp (stmt p)
expr e                          = e
