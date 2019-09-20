module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)
import Data.List  (find)

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Basic       (Proto,Protos)
import Ceu.Grammar.Type        (TypeC, show', sort', Type(..), FuncType(..), toTTuple, insTTuple, instantiate, listToType)
import Ceu.Grammar.Full.Full

idtp id tp = dollar $ id ++ "$" ++ show' tp

-------------------------------------------------------------------------------

-- Insert constraint in each nested method in outer contraint/instance.
--
--    contraint IEq        (eq,neq)
--
--    contraint IEq        (eq where a is IEq,neq where a is IEq)

insConstraint :: Stmt -> Stmt

insConstraint (SClass z cls cs ifc) =
   case Cs.toList cs of
    [(var,_)]  -> SClass z cls cs ifc' where
                    ifc' = map_stmt (f2 f, Prelude.id, Prelude.id) [] ifc
                    f (SVar z id (tp',cs') ini) = SVar z id (tp', Cs.insert (var,cls) cs') ini
                    f p = p
    otherwise  -> error "TODO: multiple vars"

insConstraint p = p

-------------------------------------------------------------------------------

-- Add list of prototypes.
--
--
-- Set type of generic var.
--
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--    func f : (a -> Int) where a is IEq
--
--    contraint IEq        (eq/GClass, neq/GClass)
--    instance  IEq for Int(eq/GInst,  neq/GInstc)
--    func f/GFunc

addProtosGen :: Stmt -> Stmt

addProtosGen (SClass z cls cs ifc) = SClass' z cls cs pts ifc'
  where
    pts  = protos ifc
    ifc' = map_stmt (f2 f, Prelude.id, Prelude.id) [] ifc where
            f (SVar' z id _ tpc ini) = SVar' z id (GClass cls cs pts) tpc ini
            f p = p

addProtosGen (SInst z cls tpc@(tp,_) imp) = SInst' z cls tpc (protos imp) imp'
  where
    imp' = map_stmt (f2 f, Prelude.id, Prelude.id) [] imp where
            f (SVar' z id _ tpc' ini) = SVar' z id (GInst cls tp) tpc' ini
            f p = p

addProtosGen (SVar z id tpc@(_,cs) ini) = SVar' z id gen tpc ini
  where
    gen = if Map.null cs then GNone
                         else GFunc [] []

addProtosGen p = p

-- convert from sequence of declarations to list of prototypes:
--    constraint IEq for a with (eq:tp1, neq:tp2)
-- becomes
--    [(.,eq,tp1,.),(.,neq,tp2,.)]

protos :: Stmt -> Protos
protos (SSeq _ p1 p2)           = Map.union (protos p1) (protos p2)
protos (SVar' z id gen tpc ini) = Map.singleton id (z,id,tpc,isJust ini)
protos p                        = Map.empty

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
    dict = SData z tpd (Just pars) tps Cs.cz False where
            pts' = Map.elems pts
            pars = map (\(_,id,_,_)->id) pts'
            tps  = listToType (map f pts') where
                    f (_,_,(TFunc ft inp out,_),_) = TFunc ft inp' out where
                                                      inp' = insTTuple (TData False [dollar id] []) (toTTuple inp)

dclClassDicts p = p

-------------------------------------------------------------------------------

-- Remove contraint/inst from the program (split actual dcls/impls from their
-- abstract prototypes).
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--
--    contraint IEq        (eq,neq) ; eq ; neq
--    instance  IEq for Int(eq,neq) ; eq ; neq

remClassInst :: Stmt -> Stmt
remClassInst (SClass' z id  ctrs pts ifc) = SSeq z (SClass'' z id  ctrs pts) ifc
remClassInst (SInst'  z cls tpc  pts imp) = SSeq z (SInst''  z cls tpc  pts)
                                            (SSeq z (STodo z "SInst-INI")
                                            (SSeq z imp (STodo z "SInst-END")))
remClassInst p = p

-------------------------------------------------------------------------------

-- Populate GFunc with Class and Instances.
--
--    constraint  IEq         (eq,neq)
--    instance of IEq for Int (eq)
--
--    instance of IEq for Int (eq(True),neq(False))

popGFunc :: [Stmt] -> Stmt -> Stmt

popGFunc env (SVarS z id (GFunc _ _) tpc@(_,cs) ini p) =
  SVarS z id (GFunc stmts itpss) tpc ini p where
    idss :: [[ID_Class]]
    idss = map Set.toList $ Map.elems cs where

    stmtss :: [[Stmt]]
    stmtss = map (map getCls) $ map Set.toList $ Map.elems cs where
              getCls cls = case find f env of
                            Just s -> s
                            -- TODO: Nothing
                           where
                            f (SClassS _ id _ _ _) = id == cls
                            f _ = False

    [stmts] = stmtss

    itpss :: [[Type]]
    itpss = sort' $ combos' 1 env idss

    -- [ [Ia], [Ib], ... ]
    -- [ [A1,A2,...], [B1,B2,...], ... ]
    -- [ [A1,B1,...], [A1,B2,...], ... ]
    combos' :: Int -> [Stmt] -> [[ID_Class]] -> [[Type]]
    combos' lvl env clss = combos insts where
      insts :: [[Type]]
      insts = map h clss
        where
          h :: [ID_Class] -> [Type]
          h [cls] = concatMap h $ map g $ filter f env where
            f :: Stmt -> Bool
            f (SInstS _ cls' (_,ctrs') _ _) = (cls == cls') && (lvl>0 || null ctrs')
            f _                             = False

            g :: Stmt -> TypeC
            g (SInstS _ _ tpc _ _) = tpc  -- types to instantiate

            -- expand types with constraints to multiple types
            -- TODO: currently refuse another level of constraints
            -- Int    -> [Int]
            -- X of a -> [X of Int, ...]
            h :: TypeC -> [Type]
            h tpc@(tp, ctrs) = if null ctrs then [tp] else insts where
              tpss  = combos' (lvl-1) env (map Set.toList $ Map.elems ctrs)
              insts = map (flip instantiate tp) $ map (zip (Map.keys ctrs)) tpss

popGFunc _ p = p

-------------------------------------------------------------------------------

-- Duplicate and rename implementation methods from xxx to _xxx.
--
--    constraint IEq(eq,neq(...))
--    func neq (x,y)            // keep just the declaration
--    func _$neq$ (x,y) do      // actual implementation (will receive $dict)
--
--    instance of IEq for Int (eq)
--    func _$eq$Int$ (x,y)      // actual implementation (will receive $dict)
--    func $eq$Int$ (x,y)       // wrapper to call _$eq$Int$ with $dict
--
--    func f x : (a -> Int) where a is IEq
--    func f (x)                // declaration
--    func _$f$ (x)             // will receive $dict // remove constraints from types
--    func $f$Int$ (x)          // wrapper to call _$f$ with $IEq$Int$

dupRenImpls :: Stmt -> Stmt

dupRenImpls (SVarS z id gen@(GClass _ _ _) tpc@(tp,_) ini p) =
  SVarS z id gen tpc Nothing $
    SVarS z ('_':dollar id) gen tpc ini $
      p

dupRenImpls (SVarS z id gen@(GInst _ itp) tpc' ini p) =
  SVarS z (idtp id itp) gen tpc' ini $
    SVarS z ('_':idtp id itp) gen tpc' ini $
      p

dupRenImpls (SVarS z id gen@(GFunc _ [[itp]]) tpc ini p) = f itp p
  where
    f :: Type -> Stmt -> Stmt
    f itp p = SVarS z id gen tpc Nothing $
                SVarS z ('_':dollar id) gen tpc (fmap remCtrs ini) $
                  SVarS z (idtp id itp) gen tpc Nothing $
                    p

    -- remove constraints since we already receive the actual $dict
    remCtrs :: Exp -> Exp
    remCtrs e = map_exp' (f2 Prelude.id, Prelude.id, (\(tp,_) -> (tp,Cs.cz))) e

{-
wrap :: [(ID_Var,Type)] -> Stmt -> Stmt -> Stmt
wrap insts (SVar z1 id1 (tp,_) (SSeq z2 (SMatch z3 True False body [(ds,EVar z4 id2,p)]) _)) acc | id1==id2 =
  SVar z1 id' (tp',cz)
    (SSeq z2
      (SMatch z3 True False body' [(ds,EVar z4 id',p)])
      acc)
  where
    id'   = idtp id1 tp'
    tp'   = T.instantiate insts tp
    body' = map_exp (Prelude.id,Prelude.id,ftp) body
      where
        ftp (tp,_) = (T.instantiate insts tp,cz)
-}

dupRenImpls p = p

-------------------------------------------------------------------------------

-- For each existing constraint/default or instance implementation, insert dict
-- wrappers for all other constraint methods.
--
--    constraint  IEq         (eq,neq(...))
--
--    func _$neq$ (x,y) do  // will receive $dict
--      $eq$ = func (x,y) do return $dict.eq($dict,x,y) end
--      ... -- one for each other method
--      ... -- original default implementation
--    end

insGenWrappers :: Stmt -> Stmt

insGenWrappers s@(SVarS z ('_':id) (GClass cls _ pts)                _ (Just _) _) = insGW (cls,pts) s
insGenWrappers s@(SVarS z ('_':id) (GFunc [SClassS _ cls _ pts _] _) _ (Just _) _) = insGW (cls,pts) s
insGenWrappers p = p

insGW (cls,pts)
      (SVarS z ('_':id) gen tpc (Just (EFunc z2 ft2 par2 p2)) p) =
  SVarS z ('_':id) gen tpc (Just (EFunc z2 ft2 par2 p2')) p where
    p2' = foldr ($) p2 (map g (filter notme (Map.elems pts))) where
            notme (_,id',_,_) = id /= id'

            g (_,id',(tp@(TFunc _ inp _),_),_) =
              SVarS z (dollar id') gen (tp,Cs.cz) -- remove cs
                (Just (EFunc z (tp,Cs.cz) (expand inp) q)) where
                  q = SRet z (ECall z
                              (ECall z (EField z [dollar cls] id') (EVar z "$dict"))
                              (insETuple (EVar z "$dict") (toETuple $ expand inp)))

            -- expand inputs:
            -- ($1,$2) = EArg
            -- call f ($dict,$1,$2)
            expand (TTuple l) = ETuple z $
                                  map (\v->EVar z v) $
                                    take (length l) $
                                      map (\v->'$':show v) $
                                        incs where
                                          incs  = 1 : map (+1) incs
            expand _ = EVar z ("$1")

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

insDict s@(SVarS _ _ GNone _ _ _) = s

insDict (SVarS z ('_':id) gen (TFunc ft1 inp1 out1,cs1)
          (Just (EFunc z2 (TFunc ft2 inp2 out2,cs2) par2  p2))
          p) =
  SVarS z ('_':id) gen (TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = insTTuple (TData False [dollar cls] []) (toTTuple inp1)
    inp2' = insTTuple (TData False [dollar cls] []) (toTTuple inp2)
    par2' = insETuple (EVar z "$dict") (toETuple par2)
    cls = case gen of
            GClass cls _ _ -> cls
            GInst  cls _   -> cls
            GFunc  [SClassS _ cls _ _ _] _ -> cls

insDict p = p

-------------------------------------------------------------------------------

-- For each existing implementation, insert dict parameters for all constraint
-- methods.
--
--    instance of IEq for Int (...,eq(x,y))
--
--    func _$eq$Int$ ($dict,x,y) return $eq$Int$(x,y)

addInstCall :: Stmt -> Stmt

addInstCall (SVarS z ('_':id) gen@(GInst _ _) tpc (Just (EFunc z2 tp2 par2 _)) p) =
  SVarS z ('_':id) gen tpc (Just (EFunc z2 tp2 par2 p2)) p where
    p2 = SRet z (ECall z (EVar z id) (remTuple par2))

    remTuple (ETuple _ [EVar _ "$dict", y])  = y
    remTuple (ETuple z (EVar _ "$dict" : l)) = ETuple z l
    remTuple x = x

addInstCall p = p

-------------------------------------------------------------------------------

-- Unite all protos from Class/Inst.
--
--    constraint  IEq         (eq,neq)
--    instance of IEq for Int (eq)
--
--    instance of IEq for Int (eq(True),neq(False))

uniInstProtos :: [Stmt] -> Stmt -> Stmt

uniInstProtos env (SInstS z cls tpc@(tp,_) pts bdy) =
  SInstS z cls tpc pts' bdy where
    pts' = case find f env of
            Just (SClassS _ _ _ x _) -> Map.union pts $ Map.map noIni $ Map.difference x pts where
                                          noIni (z,id,tpc,_) = (z,id,tpc,False)
            --_ -> error $ show (cls, env)
           where
            f (SClassS _ cls' _ _ _) = (cls == cls')
            f _                      = False

uniInstProtos _ p = p

-------------------------------------------------------------------------------

-- For each instance, add its dictionary.
-- First the dict declaration, then the instance body, then the dict assignment.
--
--    instance of IEq for Int (eq(x,y))
--
--    var $IEq$Int$ : $IEq$
--    ... // body
--    $IEq$Int$ = $IEq$(_$eq$Int$, _$neq$Int$)

addInstDicts :: Stmt -> Stmt

addInstDicts (SInstS z cls tpc@(tp,_) pts bdy) = SInstS z cls tpc pts bdy' where
  bdy' = map_stmt' (f2 f, Prelude.id, Prelude.id) bdy

  dict = dollar $ cls ++ "$" ++ show' tp

  f :: Stmt -> Stmt
  f (STodoS z "SInst-INI" p) = SVarS z dict GNone (TData False [dollar cls] [],Cs.cz) Nothing p
  f (STodoS z "SInst-END" p) = SSeq z
                                (SSet z True False
                                  (EVar z dict)
                                  (ECall z (ECons z [dollar cls]) (listToExp $ map g $ Map.elems pts)))
                                p
  f p = p

  g :: Proto -> Exp
  g (z,id,_,False) = EVar z ('_' : dollar id)
  g (z,id,_,True)  = EVar z ('_' : dollar (id++"$"++show' tp))

addInstDicts p = p

-------------------------------------------------------------------------------

-- For each missing implementation, add dummy implementation that calls
-- constraint default.
--
--    instance of IEq for Int (eq(x,y))
--
--    func $neq$Int$ (x,y) return _$neq$($IEq$Int$,x,y)

addInstMissing :: Stmt -> Stmt

addInstMissing (SInstS z cls tpc@(tp,_) pts (SVarS z2 id2 gen2 tp2 Nothing bdy)) =
  SInstS z cls tpc pts (SVarS z2 id2 gen2 tp2 Nothing bdy') where
    bdy' = foldr ($) bdy $ map g $ Map.elems $ Map.filter f pts where
            f (_,_,_,ini) = not ini   -- only methods w/o implementation

            g :: Proto -> (Stmt -> Stmt)
            g (z2,id2,tpc2@(tp2,_),False) = SVarS z2 (idtp id2 tp) gen2 tpc2' (Just (EFunc z2 tpc2' par1 p)) where
              tp2' = instantiate [("a",tp)] tp2  -- TODO: a is fixed
              (TFunc _ inp2' _) = tp2'
              tpc2' = (tp2',Cs.cz)

              p = SRet z2 (ECall z2 (EVar z2 ('_':dollar id2)) par2)

              par1 = listToExp $ map (EVar z2) $ par
              par2 = listToExp $ map (EVar z2) $ (("$"++cls++"$"++show' tp++"$") :) $ par
              par  = map ('$':) $ map show $ lns $ len $ toTTuple inp2' where
                      len (TTuple l) = length l
                      lns n = take n lns' where
                                lns' = 1 : map (+1) lns'

addInstMissing p = p

-------------------------------------------------------------------------------

-- For each missing implementation, add dummy implementation that calls
-- constraint default.
--
--    var $f$Int$ x : (Int -> Int);

--    var $f$Int$ x : (Int -> Int) do
--      return _$f$($IEq$Int,...)
--    end

addGenCall :: Stmt -> Stmt

addGenCall (SVarS z ('$':id) gen@(GFunc _ _) tpc Nothing p) =
   SVarS z ('$':id) gen tpc (Just (EFunc z tpc (EUnit z) bdy)) p where
    bdy = SRet z (ECall z (EVar z id) (EUnit z))
  --dict = dollar $ cls ++ "$" ++ show' tp
                              --(ECall z (EField z [dollar cls] id') (EVar z "$dict"))
                              --(insETuple (EVar z "$dict") (toETuple $ expand inp)))

addGenCall p = p
