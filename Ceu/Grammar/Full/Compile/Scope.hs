module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (SClass' z id  cs ifc)               = SClass'' z id  cs ifc (SNop z)
stmt (SInst'  z cls tp imp)               = SInst''  z cls tp imp (SNop z)
stmt (SData   z nms tp abs)               = SData''  z nms tp abs (SNop z)
stmt (SVar    z var tp)                   = SVar''   z var tp (SNop z)
stmt (SMatch' z ini chk exp cses)         = SMatch'  z ini chk (expr exp)
                                              (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses)
stmt (SCall  z exp)                       = SCall   z (expr exp)
stmt (SSeq _ s@(SClass' z id  cs ifc) p2) = SClass'' z id  cs ifc (stmt p2)
stmt (SSeq _ s@(SInst'  z cls tp imp) p2) = SInst''  z cls tp imp (stmt p2)
stmt (SSeq _ s@(SData   z nms tp abs) p2) = SData''  z nms tp abs (stmt p2)
stmt (SSeq _ s@(SVar    z var tp) p2)     = SVar''   z var tp (stmt p2)
stmt (SSeq    z p1 p2)                    = SSeq     z (stmt p1) (stmt p2)
stmt (SLoop   z p)                        = SLoop    z (stmt p)
stmt (SScope  _ p)                        = (stmt p)
stmt (SRet   z exp)                       = SRet     z (expr exp)
stmt p                                    = p

expr :: Exp -> Exp
expr (ETuple z es)                        = ETuple   z (map expr es)
expr (ECall  z e1 e2)                     = ECall    z (expr e1) (expr e2)
expr (EFunc  z ftp tp p)                  = EFunc    z ftp tp (stmt p)
expr e                                    = e

