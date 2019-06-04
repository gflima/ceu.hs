module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann)
import Ceu.Grammar.Type     (Type, show', hasAnyConstraint)
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

protos :: Stmt -> [(Ann, ID_Var, Type, Bool)]
protos (Seq  _ (Var z id tp) (Set _ False (LVar id') _)) | id==id' = [(z,id,tp,True)]
protos (Seq  _ p1 p2) = (protos p1) ++ (protos p2)
protos (Var z id tp)  = [(z,id,tp,False)]
protos p              = []

rename :: Stmt -> Stmt
rename (Seq  z (Var z1 id tp)
               (Set z2 False (LVar id') exp))
        | id==id'    = Seq  z (Var z1 (idtp id tp) tp)
                                     (Set  z2 False (LVar $ idtp id' tp) exp)
rename (Seq z p1 p2) = Seq  z (rename p1) (rename p2)
rename (Var z id tp) = Var z (idtp id tp) tp
rename p             = p

idtp id tp = if hasAnyConstraint tp then id else "$" ++ id ++ "$" ++ show' tp ++ "$"

stmt :: Stmt -> Stmt

stmt (Class z me exts ifc)   = Seq z (Class' z me exts (protos ifc)) ifc
stmt (Inst  z me imp)        = Seq z (Inst'  z me      (protos imp)) (rename imp)
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
