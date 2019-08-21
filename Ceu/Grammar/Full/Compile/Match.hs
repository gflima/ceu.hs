module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (SInst   z cls tp imp)    = SInst   z cls tp (stmt imp)
stmt (SSet    z ini chk pat exp) = stmt $ SMatch z ini chk exp [(SNop z,pat,SNop z)]
stmt (SMatch  z ini chk exp cses) = SMatch' z ini chk  (expr exp) (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses')
                                 where
                                  cses' = cses
                                  --cses' = if not chk then cses else
                                            --cses ++ [(EAny z, SRet z $ EError z (-2))]
stmt (SCall   z exp)           = SCall  z (expr exp)
stmt (SIf     z exp p1 p2)     = stmt $ SMatch z False False exp [
                                  (SNop z, EExp z (EVar z "_true"), stmt p1),
                                  (SNop z, EAny z,                  stmt p2)
                                 ]
stmt (SSeq    z p1 p2)         = SSeq    z (stmt p1) (stmt p2)
stmt (SLoop   z p)             = SLoop   z (stmt p)
stmt (SScope  z p)             = SScope  z (stmt p)
stmt (SRet    z exp)           = SRet    z (expr exp)
stmt p                         = p

expr :: Exp -> Exp
expr (ETuple z es)            = ETuple z (map expr es)
expr (ECall  z e1 e2)         = ECall  z (expr e1) (expr e2)
expr (EFunc' z tp imp)        = EFunc' z tp (stmt imp)
expr e                        = e
