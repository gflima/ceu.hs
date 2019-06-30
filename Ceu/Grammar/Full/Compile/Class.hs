module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann)
import Ceu.Grammar.Type     (TypeC, show')
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

protos :: Stmt -> [(Ann, ID_Var, TypeC, Bool)]
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

idtp id (tp_,ctrs) = if null ctrs then "$" ++ id ++ "$" ++ show' tp_ ++ "$" else id

stmt :: Stmt -> Stmt

stmt (Class z id  ctrs ifc)  = Seq z (Class' z id  ctrs (protos ifc)) ifc
stmt (Inst  z cls tp   imp)  = Seq z (Inst'  z cls tp   (protos imp)) (rename imp)
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
expr (ETuple z es)           = ETuple z (map expr es)
expr (ECall  z e1 e2)        = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)         = EFunc  z tp (stmt p)
expr e                       = e
