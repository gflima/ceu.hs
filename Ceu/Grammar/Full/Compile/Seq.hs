module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p
stmt :: Stmt -> Stmt
stmt (Inst   z cls tp imp)         = Inst   z cls tp (stmt imp)
stmt (Match' z chk loc exp p1 p2)  = Match' z chk loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS  z exp)                = CallS  z (expr exp)
--stmt (Seq    z (Match' z' chk loc exp p1 p2) p3) = stmt $ Match' z' chk loc exp (Seq z p1 p3) (Seq z p2 p3)
stmt (Seq    z (Match' z' False loc exp p1 p2) p3) = stmt $ Match' z' False loc exp (Seq z p1 p3) p2
stmt (Seq    z (Seq z' p1 p2) p3) = stmt $ Seq z p1 (Seq z' p2 p3)
stmt (Seq    z p1 p2)              = Seq    z (stmt p1) (stmt p2)
stmt (Loop   z p)                  = Loop   z (stmt p)
stmt (Scope  z p)                  = Scope  z (stmt p)
stmt (Ret    z exp)                = Ret  z (expr exp)
stmt p                             = p

expr :: Exp -> Exp
expr (Cons  z id e)             = Cons  z id (expr e)
expr (Tuple z es)               = Tuple z (map expr es)
expr (Call  z e1 e2)            = Call  z (expr e1) (expr e2)
expr (Func  z tp p)             = Func  z tp (stmt p)
expr e                          = e
