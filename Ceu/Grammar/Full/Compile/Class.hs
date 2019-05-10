module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann)
import Ceu.Grammar.Type     (Type)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Class z me exts ifc) = Seq z (Class' z me exts (aux ifc)) ifc
  where
    aux :: Stmt -> [(Ann, ID_Var, Type, Bool)]
    aux (Seq  _ (Var' z id _ tp) (Set _ False (LVar id') _)) | id==id' = [(z,id,tp,True)]
    aux (Seq  _ p1 p2)       = (aux p1) ++ (aux p2)
    aux (Var' z id True tp)  = [(z,id,tp,False)]
    aux p                    = []

stmt (Inst  z me imp)        = Inst  z me (stmt imp)
stmt (Set   z chk loc exp)   = Set   z chk loc (expr exp)
stmt (Match z loc exp p1 p2) = Match z loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS z exp)           = CallS z (expr exp)
stmt (If    z exp p1 p2)     = If    z (expr exp) (stmt p1) (stmt p2)
stmt (Seq   z p1 p2)         = Seq   z (stmt p1) (stmt p2)
stmt (Loop  z p)             = Loop  z (stmt p)
stmt (Scope z p)             = Scope z (stmt p)
stmt (Ret   z exp)           = Ret   z (expr exp)
stmt p                       = p

expr :: Exp -> Exp
expr (Call z e1 e2)          = Call z (expr e1) (expr e2)
expr (Func z tp p)           = Func z tp (stmt p)
expr e                       = e
