module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Class' z id  cs ifc)                    = Class'' z id  cs ifc (Nop z)
stmt (Inst'  z cls tp imp)                    = Inst''  z cls tp imp (Nop z)
stmt (Data   z tp abs)                        = Data''  z tp abs (Nop z)
stmt (Var    z var tp)                        = Var''   z var tp (Nop z)
stmt (Match' z chk loc exp p1 p2)             = Match'  z chk loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS  z exp)                           = CallS   z (expr exp)
stmt (Seq _ s@(Class' z id  cs ifc) p2)       = Class'' z id  cs ifc (stmt p2)
stmt (Seq _ s@(Inst'  z cls tp imp) p2)       = Inst''  z cls tp imp (stmt p2)
stmt (Seq _ s@(Data   z tp abs) p2)           = Data''  z tp abs (stmt p2)
stmt (Seq _ s@(Var    z var tp) p2)           = Var''   z var tp (stmt p2)
stmt (Seq    z p1 p2)                         = Seq     z (stmt p1) (stmt p2)
stmt (Loop   z p)                             = Loop    z (stmt p)
stmt (Scope  _ p)                             = (stmt p)
stmt (Ret   z exp)                            = Ret     z (expr exp)
stmt p                                        = p

expr :: Exp -> Exp
expr (ETuple z es)                            = ETuple   z (map expr es)
expr (ECall  z e1 e2)                         = ECall    z (expr e1) (expr e2)
expr (EFunc  z tp p)                          = EFunc    z tp (stmt p)
expr e                                        = e

