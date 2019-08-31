module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Set as S
import Data.Maybe (isJust)

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Type        (TypeC, show', Type(..))
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

insConstraints :: Stmt -> Stmt  -- () -> (SSeq,SVar,SFunc)

insConstraints (SClass z cls cs ifc) =
  case Cs.toList cs of
    [(var,_)]  -> SClass z cls cs (aux ifc) where
      aux (SSeq  z p1 p2)           = SSeq  z (aux p1) (aux p2)
      aux (SVar  z id (tp_,cs) ini) = SVar  z id (tp_, Cs.insert (var,cls) cs) ini
      --aux (SFunc z id (tp_,cs) par imp) = SFunc z id (tp_, Cs.insert (var,cls) cs) par imp
      aux p                     = p
    otherwise  -> error "TODO: multiple vars"

insConstraints (SInst  z cls tp@(_,cs) imp) = SInst  z cls tp (aux imp)
  where
    aux (SSeq  z p1 p2)             = SSeq  z (aux p1) (aux p2)
    aux (SVar  z id (tp_',cs') ini) = SVar  z id (tp_',Cs.union cs cs') ini
    --aux (SFunc z id (tp_',cs') par imp) = SFunc z id (tp_',Cs.union cs cs') par imp
    aux p                       = p

insConstraints p = p

-------------------------------------------------------------------------------

adjSClassSInst :: Stmt -> Stmt    -- (SClass,SInts,SSet,SVar) -> (SSeq,SData,SSet,SVar)

--adjSClassSInst (SClass z id  ctrs ifc) = SSeq z (SClass' z id  ctrs (protos ifc)) ifc

-- data _IEq ; class IEq ; Ifc ; var _IEq_int : _IEq = ...
adjSClassSInst (SClass z id ctrs ifc) = SSeq z cls ifc -- SSeq z dict (SSeq z cls (addDict tpd ifc'))
  where
    cls  = SClass' z id ctrs ps
    ps   = protos ifc
    tpd  = TData False ["_"++id] []
    dict = SData z tpd (Just $ "_dict":pars) tps Cs.cz False where
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

adjSClassSInst (SInst  z cls tp  imp)  = SSeq z (SInst' z cls tp (protos imp))
                                                (addDict (TData False ["_"++cls] []) $ renameID imp)

adjSClassSInst p = p

-------------------------------------------------------------------------------

-- convert from sequence of declarations to list of prototypes:
--    constraint IEq for a with (eq:tp1, neq:tp2)
-- becomes
--    [(.,eq,tp1,.),(.,neq,tp2,.)]

protos :: Stmt -> [(Ann, ID_Var, TypeC, Bool)]
protos (SSeq _ p1 p2)     = (protos p1) ++ (protos p2)
protos (SVar z id tp ini) = [(z,id,tp,isJust ini)]
protos p                  = []

-------------------------------------------------------------------------------

renameID :: Stmt -> Stmt
renameID (SSeq z p1 p2)     = SSeq z (renameID p1) (renameID p2)
renameID (SVar z id tp ini) = SVar z (idtp id tp) tp ini
renameID p                  = p

idtp id (tp_,ctrs) = if null ctrs then "$" ++ id ++ "$" ++ show' tp_ ++ "$" else id

-------------------------------------------------------------------------------

addDict :: Type -> Stmt -> Stmt
addDict _    p              = p
{-
addDict dict (SSeq z (SVar z1 id1 tpc1)
                     (SSet z2 True False (EVar z3 id3) (EFunc z4 tp4 par4 p4)))
             | id1==id3     = SSeq z (traceShowId $ SVar z1 id1 (aux1 dict tpc1))
                                     (SSet z2 True False (EVar z3 id3)
                                           (EFunc z4 (aux1 dict tp4) par4 (aux2 dict p4)))
addDict dict (SSeq z p1 p2) = SSeq z (addDict dict p1) (addDict dict p2)
addDict dict (SVar z id tp) = traceShowId $ SVar z id (aux1 dict tp)
addDict _    p              = p
-}

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
