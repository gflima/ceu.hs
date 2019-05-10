module Ceu.Grammar.Full.Compile.Match where

import Debug.Trace
import Ceu.Eval (error_match)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Inst   z me imp)        = Inst   z me (stmt imp)
stmt (Set    z chk loc exp)   = Match' z chk  loc (expr exp) (Nop z) (Ret z (Error z error_match))
stmt (Match  z loc exp p1 p2) = Match' z True loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS  z exp)           = CallS  z (expr exp)
stmt (If     z exp p1 p2)     = Match' z True (LExp (Read z "_true")) (expr exp)
                                              (stmt p1) (stmt p2)
stmt (Seq    z p1 p2)         = Seq    z (stmt p1) (stmt p2)
stmt (Loop   z p)             = Loop   z (stmt p)
stmt (Scope  z p)             = Scope  z (stmt p)
stmt (Ret    z exp)           = Ret    z (expr exp)
stmt p                        = p

expr :: Exp -> Exp
expr (Call z e1 e2)           = Call z (expr e1) (expr e2)
expr (Func z tp p)            = Func z tp (stmt p)
expr e                        = e
