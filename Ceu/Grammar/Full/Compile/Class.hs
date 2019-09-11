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

dclClassDicts :: Stmt -> Stmt

dclClassDicts cls@(SClass z id _ ifc) = SSeq z dict cls
  where
    ps   = protos ifc
    tpd  = TData False ['_':id] []
    dict = SData z tpd (Just $ "_dict":pars) tps Cs.cz False where
            pars = map (\(_,id,_,_)->id) ps
            tps  = TTuple (tpd : map (\(_,_,(tp,_),_)->tp) ps)

dclClassDicts p = p

-------------------------------------------------------------------------------

-- Duplicate and rename implementation methods from xxx to _xxx.
--
--    constraint IEq(eq,neq(...))
--    func neq (x,y)            // keep just the declaration
--    func _neq (x,y) do        // rename for the actual implementation
--
--    instance of IEq for Int (eq)
--    func eq_Int (x,y)         // wrapper to call _neq_Int with _dict
--    func _eq_Int (x,y)        // actual impl. with _dict

dupRenImpls :: Stmt -> Stmt

dupRenImpls (SClass z id ctrs ifc) = SClass z id ctrs ifc' where
  ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc
  f (SVar z id tpc (Just imp)) = SSeq z (SVar z id tpc Nothing)
                                        (SVar z ('_':id) tpc (Just imp))
  f p = p

dupRenImpls (SInst z cls tpc@(tp,_) imp) = SInst z cls tpc imp' where
  imp' = map_stmt (f, Prelude.id, Prelude.id) imp
  f s@(SVar z id tpc' p) = SSeq z s
                                  (SVar z ("_"++id++"_"++show' tp) tpc' p)
  f p = p

dupRenImpls p = p

-------------------------------------------------------------------------------

-- For each existing constraint/default or instance implementation, insert dict
-- wrappers for all other constraint methods.
--
--    constraint  IEq         (eq,neq(...))
--    instance of IEq for Int (eq(...))
--
--    func _neq (x,y) do
--      eq = func (x,y) do return _dict.eq(_dict,x,y) end
--      ... -- one for each other method
--      ... -- original default implementation
--    end
--
--    func eq_int (x,y) : ((Int,Int) -> Int) do
--      neq = func (x,y) do return _neq(_IEq_int,x,y) end
--      ... -- one for each other method
--      ... -- original instance implementation
--    end

insWrappers :: Stmt -> Stmt

insWrappers (SClass z cls ctrs ifc) = SClass z cls ctrs ifc' where
  ps   = protos ifc
  ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc

  f (SVar z ('_':id) tpc (Just (EFunc z2 tp2 par2 p2))) =
    SVar z id tpc (Just (EFunc z2 tp2 par2 p2')) where
      p2' = foldr (SSeq z) p2 (map g (filter notme ps)) where
              notme (_,id',_,_) = id /= ('_':id')

              g (_,id',_,_) = SVar z id' tpc (Just (EFunc z tp2 par2 p)) where
                                p = SRet z (ECall z (EField z ['_':cls] id') (insTuple z (EVar z "_dict") par2))
  f p = p

  insTuple z e (ETuple _ l)  = ETuple z (e:l)
  insTuple z e f             = ETuple z [e,f]

insWrappers (SInst z cls tpc@(tp,_) imp) = SInst z cls tpc imp' where
  ps   = protos imp
  imp' = map_stmt (f, Prelude.id, Prelude.id) imp

  f (SVar z (c:id) tpc (Just (EFunc z2 tp2 par2 p2))) | c/='_' =
    SVar z id tpc (Just (EFunc z2 tp2 par2 p2')) where
      p2' = foldr (SSeq z) p2 (map g (filter notme ps)) where
              notme (_,id',_,_) = id /= id'
              g (_,id',_,_) = SVar z id' tpc (Just (EFunc z tp2 par2 p)) where
                                p = SRet z (ECall z (EVar z ('_':id')) (insTuple z (EVar z ("_"++cls++"_"++show' tp)) par2))
  f p = p

  insTuple z e (ETuple _ l)  = ETuple z (e:l)
  insTuple z e f             = ETuple z [e,f]

insWrappers p = p

-------------------------------------------------------------------------------

-- For each existing implementation (constraint or instance), insert dict
-- parameters for all constraint methods.
--
--    constraint  IEq         (...,neq(x,y))
--    instance of IEq for Int (...,eq(x,y))
--
--    func _neq (_dict,x,y)
--    func _eq_Int (_dict,x,y)

insDict :: Stmt -> Stmt

insDict (SClass z cls ctrs ifc) = SClass z cls ctrs ifc' where
  ifc' = map_stmt (f, Prelude.id, Prelude.id) ifc

insDict (SInst z cls tpc imp) = SInst z cls tpc imp' where
  imp' = map_stmt (f, Prelude.id, Prelude.id) imp

insDict p = p

f (SVar z ('_':id) tpc (Just (EFunc z2 (TFunc ft inp  out,cs) par2  p2))) =
   SVar z ('_':id) tpc (Just (EFunc z2 (TFunc ft inp' out,cs) par2' p2)) where
  inp'  = insTupleT (TData False ['_':id] []) inp
  par2' = insTupleE z2 (EVar z "_dict") par2
--f p@(SVar z id tpc (Just (EFunc z2 tp2  par2  p2))) = traceShow id p
f p = p

insTupleT :: Type -> Type -> Type
insTupleT tp1 (TTuple l2) = TTuple (tp1:l2)
insTupleT tp1 tp2         = TTuple [tp1,tp2]

insTupleE z e1 (ETuple _ l2) = ETuple z (e1:l2)
insTupleE z e1 e2            = ETuple z [e1,e2]

-------------------------------------------------------------------------------

-- For each existing implementation (constraint or instance), insert dict
-- parameters for all constraint methods.
--
--    instance of IEq for Int (...,eq(x,y))
--
--    func _eq_Int (_dict,x,y) return eq_Int(x,y)

addInstCall :: Stmt -> Stmt

addInstCall (SInst z cls tpc imp) = SInst z cls tpc imp' where
  imp' = map_stmt (f, Prelude.id, Prelude.id) imp where
    f (SVar z ('_':id) tpc (Just (EFunc z2 tp2 par2 _))) =
       SVar z ('_':id) tpc (Just (EFunc z2 tp2 par2 p2)) where
      p2 = SRet z (ECall z (EVar z id) (remTuple par2))
    f p = p

  remTuple (ETuple _ [EVar _ "_dict", y])  = y
  remTuple (ETuple z (EVar _ "_dict" : l)) = ETuple z l

addInstCall p = p

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
protos (SSeq _ p1 p2)        = (protos p1) ++ (protos p2)
protos (SVar _ ('_':id) _ _) = []   -- ignore dups like _xxx
protos (SVar z id tp ini)    = [(z,id,tp,isJust ini)]
protos p                     = []
