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
protos (SSeq  _ (SVar z id tp) (SSet _ _ False (EVar _ id') _)) | id==id' = [(z,id,tp,True)]
protos (SSeq  _ p1 p2) = (protos p1) ++ (protos p2)
protos (SVar z id tp)  = [(z,id,tp,False)]
protos p              = []

rename :: Stmt -> Stmt
rename (SSeq z (SVar z1 id tp)
               (SSet z2 True False (EVar z3 id') exp))
        | id==id'     = SSeq  z (SVar z1 (idtp id tp) tp)
                                (SSet z2 True False (EVar z3 $ idtp id' tp) exp)
rename (SSeq z p1 p2) = SSeq  z (rename p1) (rename p2)
rename (SVar z id tp) = SVar z (idtp id tp) tp
rename p              = p

idtp id (tp_,ctrs) = if null ctrs then "$" ++ id ++ "$" ++ show' tp_ ++ "$" else id

stmt :: Stmt -> Stmt

stmt (SClass z id  ctrs ifc) = SSeq z (SClass' z id  ctrs (protos ifc)) ifc
stmt (SInst  z cls tp   imp) = SSeq z (SInst'  z cls tp   (protos imp)) (rename imp)
stmt (SSet   z ini chk loc exp)  = SSet   z ini chk loc (expr exp)
stmt (SMatch z ini chk exp cses) = SMatch z ini chk (expr exp)
                               (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses)
stmt (SCall z exp)           = SCall z (expr exp)
stmt (SIf    z exp p1 p2)    = SIf    z (expr exp) (stmt p1) (stmt p2)
stmt (SSeq   z p1 p2)        = SSeq   z (stmt p1) (stmt p2)
stmt (SLoop  z p)            = SLoop  z (stmt p)
stmt (SScope z p)            = SScope z (stmt p)
stmt (SRet   z exp)          = SRet   z (expr exp)
stmt p                       = p

expr :: Exp -> Exp
expr (ETuple z es)           = ETuple z (map expr es)
expr (ECall  z e1 e2)        = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)         = EFunc  z tp (stmt p)
expr e                       = e
