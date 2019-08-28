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

addDict :: Type -> Stmt -> Stmt
addDict _    p              = p
addDict dict (SSeq z (SVar z1 id1 tpc1)
                     (SSet z2 True False (EVar z3 id3) (EFunc' z4 tp4 p4)))
             | id1==id3     = SSeq z (traceShowId $ SVar z1 id1 (aux1 dict tpc1))
                                     (SSet z2 True False (EVar z3 id3)
                                           (EFunc' z4 (aux1 dict tp4) (aux2 dict p4)))
addDict dict (SSeq z p1 p2) = SSeq z (addDict dict p1) (addDict dict p2)
addDict dict (SVar z id tp) = traceShowId $ SVar z id (aux1 dict tp)
addDict _    p              = p

aux1 :: Type -> TypeC -> TypeC
aux1 dict (TFunc ft inp out, cs) = (TFunc ft (f dict inp) out, cs) where
  f :: Type -> Type -> Type
  --f _ tp = tp
  f dict (TTuple l) = TTuple (dict: l)
  f dict tp         = TTuple [dict,tp]

aux2 _ x = x
{-
aux2 :: Type -> Exp -> Exp
aux2 dict (EFunc ft inp out, cs) = (TFunc ft (f dict inp) out, cs) where
  f :: Type -> Type -> Type
  --f _ tp = tp
  f dict (TTuple l) = TTuple (dict: l)
  f dict tp         = TTuple [dict,tp]
-}

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

--stmt (SClass z id  ctrs ifc) = SSeq z (SClass' z id  ctrs (protos ifc)) ifc

-- data _IEq ; class IEq ; Ifc ; var _IEq_int : _IEq = ...
stmt (SClass z id ctrs ifc) = SSeq z cls ifc -- SSeq z dict (SSeq z cls (addDict tpd ifc'))
  where
    cls  = SClass' z id ctrs ps
    ps   = protos ifc
    tpd  = TData False ["_"++id] []
    dict = SData z tpd (Just $ "_dict":pars) tps cz False where
            pars = map (\(_,id,_,_)->id) ps
            tps  = TTuple (tpd : map (\(_,_,(tp,_),_)->tp) ps)

    -- (x eq y) --> (x (_IEq.eq _dict) y)
    ifc' = map_stmt (Prelude.id, f, Prelude.id) ifc where
      set :: S.Set ID_Var
      set = foldr (\(_,id,_,_) s -> S.insert id s) S.empty ps

      f :: Exp -> Exp
      f (EVar z id) = if S.member id set then
                        (ECall z (EField z ["_"++id] id) (EVar z "_dict"))
                      else
                        EVar z id
      f e           = e

stmt (SInst  z cls tp  imp)  = SSeq z (SInst' z cls tp (protos imp))
                                      (addDict (TData False ["_"++cls] []) $ renameID imp)
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
