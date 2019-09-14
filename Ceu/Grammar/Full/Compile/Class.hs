module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Map as Map
import Data.Maybe (isJust)

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Basic       (Protos)
import Ceu.Grammar.Type        (TypeC, show', Type(..), FuncType(..), toTTuple, insTTuple, instantiate)
import Ceu.Grammar.Full.Full

dollar id = "$" ++ id ++ "$"
idtp id tp = dollar $ id ++ "$" ++ show' tp

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
                    ifc' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty ifc
                    f (SVar z id (tp',cs') ini) = SVar  z id (tp', Cs.insert (var,cls) cs') ini
                    f p = p
    otherwise  -> error "TODO: multiple vars"

insConstraint (SInst z cls tp@(_,cs) imp) = SInst z cls tp imp'
  where
    imp' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty imp
    f (SVar z id (tp',cs') ini) = SVar  z id (tp', Cs.union cs cs') ini
    f p = p

insConstraint p = p

-------------------------------------------------------------------------------

-- Add list of prototypes.
--

addProtos :: Stmt -> Stmt
addProtos (SClass z cls cs ifc) = SClass' z cls cs (protos ifc) ifc
addProtos (SInst  z cls tp imp) = SInst'  z cls tp (protos imp) imp
addProtos p = p

-- convert from sequence of declarations to list of prototypes:
--    constraint IEq for a with (eq:tp1, neq:tp2)
-- becomes
--    [(.,eq,tp1,.),(.,neq,tp2,.)]

protos :: Stmt -> Protos
protos (SSeq _ p1 p2)     = Map.union (protos p1) (protos p2)
protos (SVar z id tp ini) = Map.singleton id (z,id,tp,isJust ini)
protos p                  = Map.empty

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------

-- Declare an associated dictionay for each constraint.
--
-- Each constraint (IEq(eq,neq)) has an associated "dict" (_IEq(eq,neq))
-- (actually a static struct) in which each field (_IEq.eq) corresponds to a
-- method of the same name in the constraint (IEq.eq):
--    contraint IEq(eq,neq)
--
--    data      $IEq(eq,neq)
--    contraint IEq(eq,neq)

dclClassDicts :: Stmt -> Stmt

dclClassDicts cls@(SClass' z id _ pts ifc) = SSeq z dict cls
  where
    tpd  = TData False [dollar id] []
    dict = SData z tpd (Just $ "$dict":pars) tps Cs.cz False where
            pts' = Map.elems pts
            pars = map (\(_,id,_,_)->id) pts'
            tps  = TTuple (tpd : map f pts') where
                    f (_,_,(TFunc ft inp out,_),_) = TFunc ft inp' out where
                                                      inp' = insTTuple (TData False [dollar id] []) (toTTuple inp)

dclClassDicts p = p

-------------------------------------------------------------------------------

-- Duplicate and rename implementation methods from xxx to _xxx.
--
--    constraint IEq(eq,neq(...))
--    func neq (x,y)            // keep just the declaration
--    func $neq$ (x,y) do       // dummy id to typecheck
--    func _$neq$ (x,y) do      // actual implementation (will receive $dict)
--
--    instance of IEq for Int (eq)
--    func $eq$Int$ (x,y)       // wrapper to call _$neq$Int$ with $dict
--    func _$eq$Int$ (x,y)      // actual implementation (will receive $dict)

dupRenImpls :: Stmt -> Stmt

dupRenImpls (SClass' z id ctrs pts ifc) = SClass' z id ctrs pts ifc' where
  ifc' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty ifc
  f (SVar z id tpc@(tp,_) p) = SSeq z (SVar z id tpc Nothing) $
                               SSeq z (SVar z (    idtp id tp) tpc p)
                                      (SVar z ('_':idtp id tp) tpc p)
  f p = p

dupRenImpls (SInst' z cls tpc@(tp,_) pts imp) = SInst' z cls tpc pts imp' where
  imp' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty imp
  f s@(SVar z id tpc' p) = SSeq z (SVar z (    idtp id tp) tpc' p)
                                  (SVar z ('_':idtp id tp) tpc' p)
  f p = p

dupRenImpls p = p

-------------------------------------------------------------------------------

-- For each existing constraint/default or instance implementation, insert dict
-- wrappers for all other constraint methods.
--
--    constraint  IEq         (eq,neq(...))
--
--    func _$neq$ (x,y) do  // will receive $dict
--      eq = func (x,y) do return $dict.eq($dict,x,y) end
--      ... -- one for each other method
--      ... -- original default implementation
--    end

insClassWrappers :: Stmt -> Stmt

insClassWrappers (SClass' z cls ctrs pts ifc) = SClass' z cls ctrs pts ifc' where
  ifc' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty ifc

  f (SVar z ('_':id) tpc (Just (EFunc z2 (TFunc ft inp out,cs) par2 p2))) =
    SVar z ('_':id) tpc (Just (EFunc z2 (TFunc ft inp out,cs) par2 p2')) where
      p2' = foldr (SSeq z) p2 (map g (filter notme (Map.elems pts))) where
              notme (_,id',_,_) = id /= id'

              g (_,id',_,_) = SVar z id' tpc (Just (EFunc z (TFunc FuncNested inp out,cs) (ren par2) p)) where
                                p = SRet z (ECall z
                                            (ECall z (EField z [dollar cls] id') (EVar z "$dict"))
                                            (insETuple (EVar z "$dict") (toETuple $ ren par2)))

              -- rename parameters to prevent redeclarations
              ren (EVar   z id) = EVar z ('$':id)
              ren (ETuple z l)  = ETuple z (map f l) where
                                    f (EVar z id) = EVar z ('$':id)
  f p = p

insClassWrappers p = p

-------------------------------------------------------------------------------

-- For each existing implementation (constraint or instance), insert dict
-- parameters for all constraint methods.
--
--    constraint  IEq         (...,neq(x,y))
--    instance of IEq for Int (...,eq(x,y))
--
--    func _$neq$ ($dict,x,y)
--    func _$eq$Int$ ($dict,x,y)

insDict :: Stmt -> Stmt

insDict (SClass' z cls ctrs pts ifc) = SClass' z cls ctrs pts ifc' where
  ifc' = map_stmt (f2 $ f cls, Prelude.id, Prelude.id) Map.empty ifc

insDict (SInst' z cls tpc pts imp) = SInst' z cls tpc pts imp' where
  imp' = map_stmt (f2 $ f cls, Prelude.id, Prelude.id) Map.empty imp

insDict p = p

f cls (SVar z ('_':id) (TFunc ft1 inp1 out1,cs1)
        (Just (EFunc z2 (TFunc ft2 inp2 out2,cs2) par2  p2))) =
  SVar z ('_':id) (TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (TFunc ft2 inp2' out2,cs2) par2' p2))
  where
    inp1' = insTTuple (TData False [dollar cls] []) (toTTuple inp1)
    inp2' = insTTuple (TData False [dollar cls] []) (toTTuple inp2)
    par2' = insETuple (EVar z "$dict") (toETuple par2)
--f p@(SVar z id tpc (Just (EFunc z2 tp2  par2  p2))) = traceShow id p
f _ p = p

-------------------------------------------------------------------------------

-- For each existing implementation, insert dict parameters for all constraint
-- methods.
--
--    instance of IEq for Int (...,eq(x,y))
--
--    func _$eq$Int$ ($dict,x,y) return $eq$Int$(x,y)

addInstCall :: Stmt -> Stmt

addInstCall (SInst' z cls tpc pts imp) = SInst' z cls tpc pts imp' where
  imp' = map_stmt (f2 f, Prelude.id, Prelude.id) Map.empty imp where
    f (SVar z ('_':id) tpc (Just (EFunc z2 tp2 par2 _))) =
       SVar z ('_':id) tpc (Just (EFunc z2 tp2 par2 p2)) where
      p2 = SRet z (ECall z (EVar z id) (remTuple par2))
    f p = p

  remTuple (ETuple _ [EVar _ "$dict", y])  = y
  remTuple (ETuple z (EVar _ "$dict" : l)) = ETuple z l
  remTuple x = x

addInstCall p = p

-------------------------------------------------------------------------------

-- For each instance, add its dictionary.
-- First the dict declaration, then the instance body, then the dict assignment.
--
--    instance of IEq for Int (eq(x,y))
--
--    var $IEq$Int$ : $IEq$
--    ... // body
--    $IEq$Int$ = (_$eq$Int$, _$neq$Int$)

addInstDicts :: Stmt -> Stmt

addInstDicts (SInst' z cls tpc@(tp,_) pts imp) = SInst' z cls tpc pts imp' where
  imp' = SSeq z
          (SVar z dict (TData False [dollar cls] [],Cs.cz) Nothing)
         (SSeq z
          imp
          (SSet z True False (EVar z dict) (EArg z)))
  dict = dollar $ cls ++ "$" ++ show' tp

addInstDicts p = p

-------------------------------------------------------------------------------

-- Unite all protos from Class/Inst.
--
--    constraint  IEq         (eq,neq)
--    instance of IEq for Int (eq)
--
--    instance of IEq for Int (eq(True),neq(False))

uniInstProtos :: Clss -> Stmt -> Stmt

uniInstProtos clss (SInstS z cls tpc@(tp,_) pts bdy) =
  SInstS z cls tpc pts' bdy where
    pts' = case Map.lookup cls clss of
            Just x -> Map.union pts $ Map.map noIni $ Map.difference x pts where
                        noIni (z,id,tpc,_) = (z,id,tpc,False)
            _ -> error $ show (cls, clss)

uniInstProtos _ p = p

-------------------------------------------------------------------------------

-- For each missing implementation, add dummy implementation that calls
-- constraint default.
--
--    instance of IEq for Int (eq(x,y))
--
--    func $neq$Int$ (x,y) return _$neq$($IEq$Int$,x,y)

addInstMissing :: Stmt -> Stmt

addInstMissing (SInstS z cls tpc@(tp,_) pts (SVarS z2 id2 tp2 Nothing bdy)) =
  SInstS z cls tpc pts (SVarS z2 id2 tp2 Nothing bdy') where
    bdy' = foldr ($) bdy $ map g $ Map.elems $ Map.filter f pts where
            f (_,_,_,ini) = not ini   -- only methods w/o implementation

            g :: (Ann,ID_Var,TypeC,Bool) -> (Stmt -> Stmt)
            g (z2,id2,tpc2@(tp2,_),False) = SVarS z2 (idtp id2 tp) tpc2' (Just (EFunc z2 tpc2' par1 p)) where
              tp2' = instantiate [("a",tp)] tp2  -- TODO: a is fixed
              (TFunc _ inp2' _) = tp2'
              tpc2' = (tp2',Cs.cz)

              p = SRet z2 (ECall z2 (EVar z2 ('_':idtp id2 tp2)) par2)

              par1 = listToExp $ map (EVar z2) $ par
              par2 = listToExp $ map (EVar z2) $ (("$"++cls++"$"++show' tp++"$") :) $ par
              par  = map ('$':) $ map show $ lns $ len $ toTTuple inp2' where
                      len (TTuple l) = length l
                      lns n = take n lns' where
                                lns' = 1 : map (+1) lns'

addInstMissing p = p

-------------------------------------------------------------------------------

-- Remove contraint/inst from the program (split actual dcls/impls from their
-- abstract prototypes).
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--
--    contraint IEq        (eq,neq) ; eq ; neq
--    instance  IEq for Int(eq,neq) ; eq ; neq

remClassInst :: Stmt -> Stmt
remClassInst (SClass' z id ctrs pts ifc) = SSeq z (SClass'' z id  ctrs pts) ifc
remClassInst (SInst'  z cls tp  pts imp) = SSeq z (SInst''  z cls tp   pts) imp
remClassInst p = p
