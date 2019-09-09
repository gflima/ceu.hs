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

-- Insert constraint in each nested method in outer contraint/instance.
--
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--
--    contraint IEq        (eq where a is IEq,neq where a is IEq)
--    instance  IEq for Int(eq where a is IEq,neq where a is IEq)

insConstraint :: Stmt -> Stmt

insConstraint (SClass z cls cs ifc) =
  case Cs.toList cs of
    [(var,_)]  -> SClass z cls cs ifc' where
                    ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc
                    f (SVar z id (tp',cs') ini) = SVar  z id (tp', Cs.insert (var,cls) cs') ini
                    f p = p
    otherwise  -> error "TODO: multiple vars"

insConstraint (SInst z cls tp@(_,cs) imp) = SInst z cls tp imp'
  where
    imp' = map_stmt (f, Prelude.id, Prelude.id) imp
    f (SVar z id (tp',cs') ini) = SVar  z id (tp', Cs.union cs cs') ini
    f p = p

insConstraint p = p

-------------------------------------------------------------------------------

-- Declare an associated dictionay for each constraint.
--
-- Each constraint (IEq(eq,neq)) has an associated "dict" (_IEq(eq,neq))
-- (actually a static struct) in which each field (_IEq.eq) corresponds to a
-- method of the same name in the constraint (IEq.eq):
--    contraint IEq(eq,neq)
--
--    data      _IEq(eq,neq)
--    contraint IEq(eq,neq)

dclDicts :: Stmt -> Stmt

dclDicts cls@(SClass z id _ ifc) = SSeq z dict cls
  where
    ps   = protos ifc
    tpd  = TData False ["_"++id] []
    dict = SData z tpd (Just $ "_dict":pars) tps Cs.cz False where
            pars = map (\(_,id,_,_)->id) ps
            tps  = TTuple (tpd : map (\(_,_,(tp,_),_)->tp) ps)

dclDicts p = p

-------------------------------------------------------------------------------

-- Duplicate and rename implementation methods from xxx to _xxx.
--
--    constraint IEq(eq,neq(...))
--    func neq (x,y)            // keep just the declaration
--    func _neq (x,y) do        // rename for the actual implementation
--
--    instance of IEq for Int (eq)
--    func neq_Int (x,y)        // wrapper to call _neq_Int with _dict
--    func _neq_Int (x,y)       // actual impl. with _dict

dupRenImpls :: Stmt -> Stmt

dupRenImpls (SClass z id ctrs ifc) = SClass z id ctrs ifc' where
  ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc
  f (SVar z id tpc (Just imp)) = SSeq z (SVar z id tpc Nothing)
                                        (SVar z ("_"++id) tpc (Just imp))
  f p = p

dupRenImpls (SInst z cls tpc@(tp,_) imp) = SInst z cls tpc imp' where
  imp' = map_stmt (f, Prelude.id, Prelude.id) imp
  f s@(SVar z id tpc' p) = SSeq z s (SVar z ("_"++id++"_"++show' tp) tpc' p)
  f p = p

dupRenImpls p = p

-------------------------------------------------------------------------------

-- For each existing implementation (constraint or instance), insert dict
-- wrappers for all constraint methods.
--
--    constraint IEq(eq,neq(...))
--
--    func _neq (_dict,x,y) do
--      eq = func (x,y) do return _dict.eq(_dict,x,y)
--    end

insWrappers :: Stmt -> Stmt

insWrappers (SClass z id ctrs ifc) = SClass z id ctrs ifc' where
  ps   = protos ifc
  ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc

  f (SVar z id tpc (Just (EFunc z2 tp2 par2 p2))) = SVar z id tpc (Just (EFunc z2 tp2 par2 p2')) where
    p2' = foldr (SSeq z) p2 $ map (\(_,id,_,_)->SNop z) ps
  f p = p

insWrappers p = p

-------------------------------------------------------------------------------

{-
-- Each constraint (IEq(eq,neq)) has an associated "dict" (_IEq(eq,neq))
-- (actually a static struct) in which each field (_IEq.eq) corresponds to a
-- method of the same name in the constraint (IEq.eq).
-- Each instance (IEq for Int) has a dict instance (_IEq_int) in which each
-- field (_IEq.eq) points to the actual implementation (eq_int).
-- data _IEq ; contraint IEq ; Ifc ; var _IEq_int : _IEq = ...

adjSClassSInst :: Stmt -> Stmt

--adjSClassSInst (SClass z id  ctrs ifc) = SSeq z (SClass' z id  ctrs (protos ifc)) ifc
--adjSClassSInst (SClass z id ctrs ifc) = SSeq z cls ifc

adjSClassSInst (SClass z id ctrs ifc) = SClass z id ctrs (insDict ifc)
  where
    cls  = SClass' z id ctrs ps
    ps   = protos ifc
    tpd  = TData False ["_"++id] []
    dict = SData z tpd (Just $ "_dict":pars) tps Cs.cz False where
            pars = map (\(_,id,_,_)->id) ps
            tps  = TTuple (tpd : map (\(_,_,(tp,_),_)->tp) ps)

    -- (x eq y) --> (x (_IEq.eq _dict) y)
    ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc where
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
-}

-------------------------------------------------------------------------------

-- Remove contraint/inst from the program (split actual dcls/impls from their
-- abstract prototypes).
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--
--    contraint IEq        (eq,neq) ; eq ; neq
--    instance  IEq for Int(eq,neq) ; eq ; neq

remClassInst :: Stmt -> Stmt
remClassInst (SClass z id ctrs ifc) = traceStmt $ SSeq z (SClass' z id  ctrs (protos ifc)) ifc
remClassInst (SInst  z cls tp  imp) = traceStmt $ SSeq z (SInst'  z cls tp   (protos imp)) imp
remClassInst p = p

-------------------------------------------------------------------------------
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

{--

renameID :: Stmt -> Stmt
renameID (SSeq z p1 p2)     = SSeq z (renameID p1) (renameID p2)
renameID (SVar z id tp ini) = SVar z (idtp id tp) tp ini
renameID p                  = p

idtp id (tp_,ctrs) = if null ctrs then "$" ++ id ++ "$" ++ show' tp_ ++ "$" else id

-------------------------------------------------------------------------------

-- Each method needs to receive an extra "_dict" argument to access the other
-- methods of the constraint.
--  eq : Int -> Int
--  eq : (_IEq,Int) -> Int

addDict :: Type -> Stmt -> Stmt
{-
addDict _    p              = p
-}
addDict dict (SVar z1 id1 tpc1 (Just (EFunc z2 tp2 par2 p2)))
                                    = SVar z1 id1 (aux1 dict tpc1)
                                        (Just $ EFunc z2 (aux1 dict tp2) par2 (aux2 dict p2))
addDict dict (SVar z id tp Nothing) = SVar z id (aux1 dict tp) Nothing
addDict dict (SSeq z p1 p2)         = SSeq z (addDict dict p1) (addDict dict p2)
addDict _    p                      = p

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

--}
