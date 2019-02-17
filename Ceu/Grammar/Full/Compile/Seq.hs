module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Class  z me  ext  ifc)       = Class z me ext (stmt ifc)
stmt (Inst   z me  imp)            = Inst  z me     (stmt imp)
stmt (Match' z chk loc exp p1 p2)  = Match' z chk loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS  z exp1 exp2)          = CallS z (expr exp1) (expr exp2)
stmt (Seq    z (Match' z' chk loc exp p1 p2) p3) = stmt $ Match' z' chk loc exp (Seq z p1 p3) p2
stmt (Seq    z (Seq z' p1 p2) p3) = stmt $ Seq z p1 (Seq z' p2 p3)
stmt (Seq    z p1 p2)              = Seq z (stmt p1) (stmt p2)
stmt (Loop   z p)                  = Loop z (stmt p)
stmt (Scope  z p)                  = Scope z (stmt p)
stmt (Ret    z exp)                = Ret z (expr exp)
stmt p                             = p

expr :: Exp -> Exp
expr (Call z e1 e2)             = Call z (expr e1) (expr e2)
expr (Func z tp p)              = Func z tp (stmt p)
expr e                          = e
