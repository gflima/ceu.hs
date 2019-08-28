module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints (cz)
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Type        (TypeC, show', Type(..))
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt p

-------------------------------------------------------------------------------

-- convert from sequence of declarations to list of prototypes:
--    constraint IEq for a with (eq:tp1, neq:tp2)
-- becomes
--    [(.,eq,tp1,.),(.,neq,tp2,.)]

protos :: Stmt -> [(Ann, ID_Var, TypeC, Bool)]
protos (SSeq  _ (SVar z id tp) (SSet _ _ False (EVar _ id') _)) | id==id' = [(z,id,tp,True)]
protos (SSeq  _ p1 p2) = (protos p1) ++ (protos p2)
protos (SVar z id tp)  = [(z,id,tp,False)]
protos p              = []

-------------------------------------------------------------------------------

renameID :: Stmt -> Stmt
renameID (SSeq z (SVar z1 id tp)
                 (SSet z2 True False (EVar z3 id') exp))
          | id==id'     = SSeq z (SVar z1 (idtp id tp) tp)
                                 (SSet z2 True False (EVar z3 $ idtp id' tp) exp)
renameID (SSeq z p1 p2) = SSeq z (renameID p1) (renameID p2)
renameID (SVar z id tp) = SVar z (idtp id tp) tp
renameID p              = p

idtp id (tp_,ctrs) = if null ctrs then "$" ++ id ++ "$" ++ show' tp_ ++ "$" else id

-------------------------------------------------------------------------------

addDict :: ID_Data -> Stmt -> Stmt
addDict dict (SSeq z (SVar z1 id1 tpc1)
                     (SSet z2 True False (EVar z3 id3) (EFunc' z4 tp4 p4)))
             | id1==id3     = SSeq z (SVar z1 id1 (addDict' dict tpc1))
                                     (SSet z2 True False (EVar z3 id3)
                                           (EFunc' z4 (addDict' dict tp4) p4))
addDict dict (SSeq z p1 p2) = SSeq z (addDict dict p1) (addDict dict p2)
addDict dict (SVar z id tp) = SVar z id (addDict' dict tp)
addDict _    p              = p

addDict' :: ID_Data -> TypeC -> TypeC
addDict' dict tpc = tpc

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (SClass z id  ctrs ifc) = SSeq z cls (SSeq z dict (addDict "XXX" ifc)) where
                                cls  = SClass' z id ctrs ps
                                ps   = protos ifc
                                dict = SData z tdat (Just $ "_dict":pars) tps cz False where
                                        tdat = TData False ["_"++id] []
                                        pars = map (\(_,id,_,_)->id) ps
                                        tps  = TTuple (tdat : map (\(_,_,(tp,_),_)->tp) ps)
--stmt (SClass z id  ctrs ifc) = SSeq z (SClass' z id  ctrs (protos ifc)) ifc
stmt (SInst  z cls tp   imp) = SSeq z (SInst'  z cls tp   (protos imp)) (addDict "XXX" $ renameID imp)
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
expr (EFunc' z tp imp)       = EFunc' z tp (stmt imp)
expr e                       = e
