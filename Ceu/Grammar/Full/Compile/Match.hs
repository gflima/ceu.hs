module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Inst   z cls tp imp)    = Inst   z cls tp (stmt imp)
stmt (Set    z False pat exp) = Match' z False (expr exp) [(pat,Nop z)]
stmt (Set    z True  pat exp) = Match' z True  (expr exp) [(pat,Nop z),(EAny z,Ret z (EError z error_match))]
stmt (Match  z exp cses)      = Match' z True (expr exp)
                                  (map (\(pt,st) -> (expr pt, stmt st)) cses)
stmt (CallS  z exp)           = CallS  z (expr exp)
stmt (If     z exp p1 p2)     = Match' z True (expr exp) [
                                  (EExp z (EVar z "_true"), stmt p1),
                                  (EAny z,                  stmt p2)
                                ]
stmt (Seq    z p1 p2)         = Seq    z (stmt p1) (stmt p2)
stmt (Loop   z p)             = Loop   z (stmt p)
stmt (Scope  z p)             = Scope  z (stmt p)
stmt (Ret    z exp)           = Ret    z (expr exp)
stmt p                        = p

expr :: Exp -> Exp
expr (ETuple z es)            = ETuple z (map expr es)
expr (ECall  z e1 e2)         = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)          = EFunc  z tp (stmt p)
expr e                        = e
