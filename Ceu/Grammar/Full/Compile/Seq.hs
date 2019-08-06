module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (SInst   z cls tp imp)        = SInst   z cls tp (stmt imp)
stmt (SMatch' z ini chk exp cses)  = SMatch' z ini chk (expr exp)
                                      (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses)
stmt (SCall  z exp)                = SCall  z (expr exp)
--stmt (SSeq    z (SMatch' z' False exp ((pat1,st1):l)) p) = stmt $ SMatch' z' False exp ((pat1,(SSeq z st1 p)):l)
stmt (SSeq    z (SSeq z' p1 p2) p3) = stmt $ SSeq z p1 (SSeq z' p2 p3)
stmt (SSeq    z p1 p2)             = SSeq    z (stmt p1) (stmt p2)
stmt (SLoop   z p)                 = SLoop   z (stmt p)
stmt (SScope  z p)                 = SScope  z (stmt p)
stmt (SRet    z exp)               = SRet  z (expr exp)
stmt p                             = p

expr :: Exp -> Exp
expr (ETuple z es)              = ETuple z (map expr es)
expr (ECall  z e1 e2)           = ECall  z (expr e1) (expr e2)
expr (EFunc' z tp imp)          = EFunc' z tp (stmt imp)
expr e                          = e
