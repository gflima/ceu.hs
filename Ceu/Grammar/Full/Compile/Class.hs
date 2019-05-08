module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Class z me exts ifc)   = Class z me exts (f ifc) (Nop z)
  where
    f (Var z id False tp (Match z2 (LVar id') exp t f)) p | id==id' =
      Var z id (Type.addConstraint (var,cls) tp) (Match z2 (LVar id') exp (f t p) f)
    f (Var z id False tp q) p =
      Var z id (Type.addConstraint (var,cls) tp) (f q p)
    f (Nop _) = p

stmt (Inst  z me imp)        = Inst  z me     (stmt imp)
stmt (Set   z chk loc exp)   = Set z chk loc (expr exp)
stmt (Match z loc exp p1 p2) = Match z loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS z exp)           = CallS z (expr exp)
stmt (If    z exp p1 p2)     = If z (expr exp) (stmt p1) (stmt p2)
stmt (Seq   z p1 p2)         = Seq z (stmt p1) (stmt p2)
stmt (Loop  z p)             = Loop z (stmt p)
stmt (Scope z p)             = Scope z (stmt p)
stmt (Ret   z exp)           = Ret z (expr exp)
stmt p                       = p

expr :: Exp -> Exp
expr (Call z e1 e2)          = Call z (expr e1) (expr e2)
expr (Func z tp p)           = Func z tp (stmt p)
expr e                       = 
