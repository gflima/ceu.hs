module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Inst   z cls tp imp)    = Inst   z cls tp (stmt imp)
stmt (Set    z chk pat exp)   = stmt $ Match z chk exp [(pat,Nop z)]
stmt (Match  z chk exp cses)  = Match' z chk  (expr exp) (map (\(pt,st) -> (expr pt, stmt st)) cses')
                                where
                                  cses' = if not chk then cses else
                                            cses ++ [(EAny z, Ret z $ EError z (-2))]
stmt (CallS  z exp)           = CallS  z (expr exp)
stmt (If     z exp p1 p2)     = stmt $ Match z False exp [
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
