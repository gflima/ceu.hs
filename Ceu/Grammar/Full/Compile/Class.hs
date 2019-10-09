module Ceu.Grammar.Full.Compile.Class where

import Data.Bool (bool)
import Data.Maybe (isJust)
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import qualified Data.List as List

--import Debug.Trace
import Ceu.Trace
import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann, toError)
import qualified Ceu.Grammar.Type as T
import Ceu.Grammar.Full.Full

toGDcls :: Stmt -> [Stmt]
toGDcls s@(SVarSG _ _ (GCls _) _ _ p) = s : toGDcls p
toGDcls s@(SVarSG _ _ GIns     _ _ p) = s : toGDcls p
toGDcls s@(SVarSG _ _ _        _ _ p) = toGDcls p
toGDcls   (SNop   _)              = []

toName :: Stmt -> ID_Var
toName (SVarSG _ id _ _ _ _) = id

getSups :: [Stmt] -> ID_Class -> [ID_Class]
getSups env cls = cls :
  case List.find (isClass cls) env of
    Nothing -> []
    Just (SClassS _ _ cs _ _) ->
      case cs of
        []         -> []
        [(_,sups)] -> foldr (\sup l -> getSups env sup ++ l) [] sups

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Insert interface in each nested method in outer contraint/implementation.
-- Do not recurse into bodies with map_stmt.
--
--    contraint IEq (eq,neq)
--    contraint IEq (eq where a is IEq,neq where a is IEq)
--
--    contraint IOrd a where a is IEq (lt,gt)
--    contraint IOrd a where a is IEq (lt where a is (IEq,IOrd),...)
--
--    instance of IEq a where a is IXx
--    func eq (x,y) : ((a,a) -> Int where a is IXx)

addClassCs :: Stmt -> Stmt

addClassCs (SClassS z cls cs ifc p) = SClassS z cls cs (f ifc) p
  where
    [(var,_)] = cs
    f :: Stmt -> Stmt
    f (SVarS z id tpc ini p) = SVarS z id (g tpc) ini (f p) where
                                g (tp,cs) = (tp, foldr (\cls cs->Cs.insert (var,cls) cs) cs [cls])
    f s@(SNop _) = s

addClassCs (SInstS z cls itpc@(_,cs) imp p) = SInstS z cls itpc (f imp) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc ini p) = --traceShow ("AAA", id, g tpc)
      SVarS z id (g tpc) ini (f p) where
        g :: T.TypeC -> T.TypeC
        g (tp1,cs1) = (tp1, foldr h cs1 cs) where
                        h :: (ID_Var,[ID_Class]) -> Cs.Map -> Cs.Map
                        h (var,clss) cs = foldr i cs clss where
                          i :: ID_Class -> Cs.Map -> Cs.Map
                          i cls cs = Cs.insert (var,cls) cs
    f s@(SNop _) = s

addClassCs p = p

-------------------------------------------------------------------------------

-- Set type of generic var.
--
--    contraint IEq        (eq,neq)
--    implementation  IEq for Int(eq,neq)
--    func f : (a -> Int) where a is IEq
--
--    contraint IEq        (eq/GCls, neq/GClass)
--    implementation  IEq for Int(eq/GInst,  neq/GInstc)
--    func f/GFunc

setGen :: Stmt -> Stmt

setGen (SClassS z cls cs ifc p) = SClassS z cls cs (f ifc) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc         Nothing    p) = SVarSG z id (GCls False) tpc Nothing $
                                                f p
    f (SVarS z id tpc@(tp,cs) (Just ini) p) = SVarSG z ('_':dol id) (GImp False id []) tpc (Just ini) $
                                                SVarSG z id (GCls True) tpc Nothing $
                                                  f p
    f s@(SNop _) = s

setGen (SInstS z cls itpc imp p) = SInstS z cls itpc (f imp) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc@(tp,cs) (Just ini) p) = SVarSG z ('_' : dols [id,T.showC itpc]) (GImp True id []) (tp,[("$",[cls])]) (Just ini) $
                                                SVarSG z id GIns tpc Nothing $
                                                  SVarSG z id (GCall [cls] itpc True) tpc Nothing $
                                                    f p
    f s@(SNop _) = s

setGen p = p

-------------------------------------------------------------------------------

setGen' :: Stmt -> Stmt
setGen' (SVarS z id tpc@(_,[]) ini p) = SVarSG z id GNone tpc ini p
setGen' (SVarS z id tpc        ini p) = SVarSG z ('_':dol id) (GImp False id []) tpc (remCs ini) $
                                          SVarSG z id (GCls $ isJust ini) tpc Nothing $
                                            p
  where
    remCs :: Maybe Exp -> Maybe Exp
    remCs (Just (EFunc z (tp,_) ps bd)) = Just (EFunc z (tp,Cs.cz) ps bd)

setGen' p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

withEnvS :: [Stmt] -> Stmt -> (Errors,Stmt)

withEnvS env s@(SClassS z cls cs ifc p) = (es1++es2++es3++es4, SClassS z cls cs ifc' p') where
                                            es1        = chkClass env z cls
                                            es2        = chkClassSupsDeclared env z cs
                                            (es3,ifc') = withEnvS (s:env) ifc
                                            (es4,p')   = withEnvS (s:env) p

withEnvS env s@(SInstS z cls tpc imp p) = (es1++es2++es3++es4++es5++es6++es7++es8,
                                           addClassGensToInst env $ SInstS z cls tpc imp' p') where
                                            es1        = chkInstClass        env z cls
                                            es2        = chkInstDeclared     env z (cls,tpc)
                                            es3        = chkInstSupsDeclared env z (cls,tpc)
                                            es4        = chkInstMissing      env z (cls,imp)
                                            es5        = chkInstUnexpected   env z (cls,imp)
                                            es6        = chkInstSignatures   env z (cls,tpc,imp)
                                            (es7,imp') = withEnvS (s:env) imp
                                            (es8,p')   = withEnvS (s:env) p

withEnvS env (SDataS z tp nms st cs abs p) = (es, SDataS z tp nms st cs abs p') where
                                              (es,p') = withEnvS env p

withEnvS env (SMatch z ini chk exp cses) = (es1 ++ concat ess, SMatch z ini chk exp' cses')
  where
    (es1,exp') = withEnvE env exp
    (ess,cses') = unzip $ map f cses
    f (ds,pt,st) = (es1++es2++es3, (ds', pt', st')) where
                    (es1,ds') = withEnvS env ds
                    (es2,pt') = withEnvE env pt
                    (es3,st') = withEnvS env st

withEnvS env (SIf z exp p1 p2) = (es1++es2++es3, SIf z exp' p1' p2') where
                                  (es1,exp') = withEnvE env exp
                                  (es2,p1')  = withEnvS env p1
                                  (es3,p2')  = withEnvS env p2

withEnvS env (SSeq z p1 p2) = (es1++es2, SSeq z p1' p2') where
                                (es1,p1') = withEnvS env p1
                                (es2,p2') = withEnvS env p2

withEnvS env (SLoop z p) = (es, SLoop z p') where
                            (es,p') = withEnvS env p

withEnvS env (SVarSG z id (GImp ins xxx []) tpc@(tp,cs) (Just ini) p) =
  (es1++es2, SVarSG z id (GImp ins xxx clss) (tp,Cs.cz) (Just $ f ini') p')
  where
    (es1,ini') = withEnvE env ini
    (es2,p')   = withEnvS env p
    clss = getSups env cls
    [(_,[cls])] = cs

    f = bool (addGGenWrappers env clss) Prelude.id ins

withEnvS env s@(SVarSG z id (GCls def) tpc Nothing p) =
  (es, repGGenInsts env $ SVarSG z id (GCls def) tpc Nothing p')
  where
    (es,p') = withEnvS (s:env) p

withEnvS env s@(SVarSG z id GIns tpc Nothing p) =
  (es, SVarSG z id GIns tpc Nothing p')
  where
    (es,p') = withEnvS (s:env) p

withEnvS env (SVarSG z id (GCall [cls] itpc has) tpc Nothing p) =
  (es, SVarSG z id (GCall (getSups env cls) itpc has) tpc Nothing p')
  where
    (es,p') = withEnvS env p

withEnvS env (SVarSG z id GNone tpc ini p) =
  (es1++es2, SVarSG z id GNone tpc ini' p')
  where
    (es1,ini') = case ini of
                  Nothing -> ([], Nothing)
                  Just x  -> (i, Just j) where (i,j) = withEnvE env x
    (es2,p')   = withEnvS env p

withEnvS env p = ([], p)

-------------------------------------------------------------------------------

withEnvE :: [Stmt] -> Exp -> (Errors,Exp)

withEnvE env (ETuple z exps)     = (concat ess, ETuple z ss) where
                                    (ess,ss) = unzip $ map (withEnvE env) exps

withEnvE env (EFunc  z tp ps bd) = (es1++es2, EFunc z tp ps' bd') where
                                    (es1,ps') = withEnvE env ps
                                    (es2,bd') = withEnvS env bd

withEnvE env (ECall  z e1 e2)    = (es1++es2, ECall z e1' e2') where
                                    (es1,e1') = withEnvE env e1
                                    (es2,e2') = withEnvE env e2

withEnvE env exp                 = ([], exp)

-------------------------------------------------------------------------------

chkClass :: [Stmt] -> Ann -> ID_Class -> Errors
chkClass env z cls =
  case List.find (isClass cls) env of
    Nothing -> []
    Just _  -> [toError z $ "interface '" ++ cls ++ "' is already declared"]

chkClassSupsDeclared :: [Stmt] -> Ann -> Cs.Map -> Errors
chkClassSupsDeclared env z cs =
  case cs of
    [(_,sups)] -> concatMap f sups where
      f sup = case List.find (isClass sup) env of
        Nothing -> [toError z $ "interface '" ++ sup ++ "' is not declared"]
        Just _  -> []
    otherwise  -> error "TODO: multiple vars"

chkInstClass :: [Stmt] -> Ann -> ID_Class -> Errors
chkInstClass env z cls =
  case List.find (isClass cls) env of
    Nothing -> [toError z $ "interface '" ++ cls ++ "' is not declared"]
    Just _  -> []

chkInstDeclared :: [Stmt] -> Ann -> (ID_Class,T.TypeC) -> Errors
chkInstDeclared env z (cls,itpc) =
  case List.find f env of
    Nothing -> []
    Just _  -> [toError z $ "implementation of '" ++ cls ++ "' for '" ++ T.showC itpc ++ "' is already declared"]
  where
    f (SInstS _ id tpc _ _) = (cls==id && itpc==tpc)
    f _ = False

-- check extends
--  interface      (Eq  for a)
--  implementation (Eq  for Bool)                  <-- so Bool must implement Eq
--  interface      (Ord for a) extends (Eq for a)  <-- but Ord extends Eq
--  implementation (Ord for Bool)                  <-- Bool implements Ord
chkInstSupsDeclared :: [Stmt] -> Ann -> (ID_Class,T.TypeC) -> Errors
chkInstSupsDeclared env z (cls,itpc) =
  case List.find (isClass cls) env of
    Nothing                   -> []   -- cls is not declared (checked before)
    Just (SClassS _ _ cs _ _) ->
      case cs of
        [(_,sups)] -> concatMap f sups where
          f :: ID_Class -> Errors
          f sup = case List.find (isInstOf sup itpc) env of
            Nothing -> [toError z $ "implementation '" ++ sup ++ " for " ++
                        (T.showC itpc) ++ "' is not declared"]
            Just _  -> []
          isInstOf x y (SInstS _ x' y' _ _) = (x'==x && y' `T.isSupOfC` y)
          isInstOf _ _ _                    = False

chkInstMissing :: [Stmt] -> Ann -> (ID_Class,Stmt) -> Errors
chkInstMissing env z (cls,imp) = concatMap toErr $ Set.toList $
                                  Set.difference
                                    (Set.fromList $ map toName $ filter isDef ifc)
                                    (Set.fromList $ map toName $ toGDcls imp)
  where
    toErr id = [toError z $ "missing implementation of '" ++ id ++ "'"]
    ifc = case List.find (isClass cls) env of
            Nothing                    -> []   -- cls is not declared (checked before)
            Just (SClassS _ _ _ ifc _) -> toGDcls ifc

    isDef (SVarSG _ _ (GCls def) _ _ _) = (not def)

chkInstUnexpected :: [Stmt] -> Ann -> (ID_Class,Stmt) -> Errors
chkInstUnexpected env z (cls,imp) = concatMap toErr $ Set.toList $
                                      Set.difference (Set.fromList $ map toName $ toGDcls imp)
                                                     (Set.fromList $ map toName ifc)
  where
    toErr id = [toError z $ "unexpected implementation of '" ++ id ++ "'"]
    ifc = case List.find (isClass cls) env of
            Nothing                    -> []   -- cls is not declared (checked before)
            Just (SClassS _ _ _ ifc _) -> toGDcls ifc

chkInstSignatures :: [Stmt] -> Ann -> (ID_Class,T.TypeC,Stmt) -> Errors
chkInstSignatures env z (cls,(itp,_),imp) = concat $ Map.elems $
                                              Map.intersectionWith chk (Map.fromList $ map toZIdTpc $ ifc)
                                                                       (Map.fromList $ map toZIdTpc $ toGDcls imp)
  where
    (var,ifc) = case List.find (isClass cls) env of
                  Nothing                     -> ("",[])   -- cls is not declared (checked before)
                  Just (SClassS _ _ cs ifc _) -> (var, toGDcls ifc) where
                                                  [(var,_)] = cs

    toZIdTpc :: Stmt -> (ID_Var, (Ann,ID_Var,T.TypeC))
    toZIdTpc (SVarSG z id _ tpc _ _) = (id, (z,id,tpc))

    chk :: (Ann,ID_Var,T.TypeC) -> (Ann,ID_Var,T.TypeC) -> Errors
    chk (_,_,tpc1) (z2,id2,tpc2) =
      case T.relatesC T.SUP tpc1 tpc2 of
        Left es -> map (toError z2) es
        Right (_,insts) ->
          let tp' = T.instantiate insts (T.TVar False var) in
            if tp' == itp then
              []
            else
              [toError z $ "types do not match : expected '" ++
                (T.show' itp) ++ "' : found '" ++
                (T.show' tp') ++ "'"]

isClass :: ID_Class -> Stmt -> Bool
isClass id1 (SClassS _ id2 _ _ _) = (id1 == id2)
isClass _   _                     = False

-------------------------------------------------------------------------------

addClassGensToInst :: [Stmt] -> Stmt -> Stmt
addClassGensToInst env s@(SInstS z cls tpc imp p) = SInstSC z (getSups env cls,ifc,gens) tpc imp p
  where
    ifc = case List.find f env of
            Nothing                    -> SNop z -- class is not declared (checked before)
            Just (SClassS _ _ _ ifc _) -> ifc
          where
            f (SClassS _ id _ _ _) = id == cls
            f _ = False
    gens = filter f env where
            f (SVarSG _ id (GCls _) (_,cs) _ _) = (cls == cls') where
                                                    [(_,[cls'])] = cs
            f _ = False
addClassGensToInst _ p = p

-------------------------------------------------------------------------------

-- For each existing interface/default or implementation implementation, insert dict
-- wrappers for all other interface methods.
--
--    interface  IEq (eq,neq(...))
--
--    func _$neq$ (x,y) do  // will receive $dict
--      $eq$ = func (x,y) do return $dict.eq($dict,x,y) end
--      ... -- one for each other method
--      ... -- original default implementation
--    end

addGGenWrappers :: [Stmt] -> [ID_Class] -> Exp -> Exp

addGGenWrappers env clss (EFunc z tpc par p) = EFunc z tpc par p' where
  p' = foldr ($) p (concat $ map cls2wrappers clss')

  clss' = concat $ map f clss where
            f cls = case List.find g env of
                      Nothing -> []
                      Just s  -> [s]
                    where
                      g (SClassS _ id _ _ _) = id == cls
                      g _ = False

  cls2wrappers :: Stmt -> [Stmt -> Stmt]
  cls2wrappers (SClassS _ cls cs ifc _) = map f $ toGDcls ifc where
    [(_,sups)] = cs

    f :: Stmt -> (Stmt -> Stmt)
    f (SVarSG _ id (GCls _) (tp@(T.TFunc _ inp _),_) _ _) =
      SVarSG z (dol id) GNone (tp,Cs.cz) $          -- remove cs
        Just (EFunc z (tp,Cs.cz) (expand inp) body)
      where
        body = SRet z (ECall z
                        (ECall z (EField z [dol cls] id) (EVar z $ dols ["dict",cls]))
                        (foldr (\cls->insETuple (EVar z $ dols ["dict",cls])) (toETuple $ expand inp) (cls:sups)))

    -- expand inputs:
    -- ($1,$2) = EArg
    -- call f ($dict,$1,$2)
    expand (T.TTuple l) = ETuple z $
                            map (\v->EVar z v) $
                              take (length l) $
                                map (\v->dol $ show v) $
                                  incs where
                                    incs  = 1 : map (+1) incs
    expand _ = EVar z ("$1")

-------------------------------------------------------------------------------

-- Create one copy for each implementation of interface.
--
--    func f x : (a -> Int) where a is IEq
--    func f (x)                // declaration
--    func _$f$ (x)             // will receive $dict // remove interfaces from types
--    func $f$Int$ (x)          // wrapper to call _$f$ with $IEq$Int$
--    func $f$Bool$ (x)         // wrapper to call _$f$ with $IEq$Bool$
--    ...

repGGenInsts :: [Stmt] -> Stmt -> Stmt
repGGenInsts env (SVarSG z id gen tpc@(tp,cs) Nothing p) =
  SVarSG z id gen tpc Nothing $
    foldr f p $ zip stmtss itpcss
  where
    -- one F for each implementation

    f :: ([Stmt],[T.TypeC]) -> Stmt -> Stmt
    f ([SClassS _ cls _ _ _],[itpc]) p =
      SVarSG z id (GCall [cls] itpc False) tpc' Nothing p where
        tpc' = T.instantiateC [("a",itpc)] tp

    idss :: [[ID_Class]]
    idss = map snd cs

    stmtss :: [[Stmt]]
    stmtss = map (map getCls) $ map snd cs where
              getCls cls = case List.find f env of
                            Just s -> s
                            -- TODO: Nothing
                           where
                            f (SClassS _ id _ _ _) = id == cls
                            f _ = False

    -- TODO: single dict
    [stmts] = stmtss

    itpcss :: [[T.TypeC]]
    --itpcss = T.sort' $ combos' 1 env idss
    itpcss = combos' 1 env idss

    -- [ [Ia], [Ib], ... ]
    -- [ [A1,A2,...], [B1,B2,...], ... ]
    -- [ [A1,B1,...], [A1,B2,...], ... ]
    combos' :: Int -> [Stmt] -> [[ID_Class]] -> [[T.TypeC]]
    combos' lvl env clsss = combos (map f1 clsss) where

      f1 :: [ID_Class] -> [T.TypeC]
      f1 clss = foldr1 List.intersect $     -- [B]
                  map f2 clss               -- [ [A,B], [B], [A,B] ]

      f2 :: ID_Class -> [T.TypeC]
      f2 cls = concat $ map h $ map g $ filter f env where
        f :: Stmt -> Bool
        f (SInstS _ cls' (_,cs') _ _) = (cls == cls') && (lvl>0 || null cs')
        f _                           = False

        g :: Stmt -> T.TypeC
        g (SInstS _ _ tpc _ _) = tpc  -- types to instantiate

        -- expand types with interfaces to multiple types
        -- TODO: currently refuse another level of interfaces
        -- Int    -> [Int]
        -- X of a -> [X of Int, ...]
        h :: T.TypeC -> [T.TypeC]
        h tpc@(tp,cs) = if null cs then [tpc] else insts where
          tpcss :: [[T.TypeC]]
          tpcss = combos' (lvl-1) env (map snd cs)
          insts :: [T.TypeC]
          insts = map (flip T.instantiateC tp) $ map (zip (map fst cs)) tpcss

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Add missing interface methods and generic functions to implementation.
--
--    interface IEq (eq,neq)
--    func f (x) where x is IEq
--    implementation of IEq for Int (eq)
--
--    implementation of IEq for Int (eq(Just),neq(Nothing),f(Nothing))

addInstGCalls :: Stmt -> Stmt

addInstGCalls (SInstSC z (clss,ifc,gens) itpc imp p) =
  SInstSC z (clss,ifc,gens) itpc imp' p where
    dif  = Set.difference (Set.fromList $ map toName $ toGDcls ifc) (Set.fromList $ map toName $ toGDcls imp)

    all  = gens ++ filter f (toGDcls ifc) where
            f (SVarSG _ id _ _ _ _) = elem id dif

    imp' = foldr ($) imp (map f all) where
            f :: Stmt -> (Stmt -> Stmt)
            f (SNop _) = Prelude.id
            f (SVarSG z2 id2 gen2 tpc2@(tp2,_) _ _) =
              SVarSG z2 id2 (GCall clss itpc False) tpc2' Nothing where
                tpc2' = T.instantiateC [("a",itpc)] tp2  -- TODO: a is fixed
                (T.TFunc _ inp2' _, _) = tpc2'

addInstGCalls p = p

-------------------------------------------------------------------------------

-- For each missing implementation, add dummy implementation that calls
-- interface default.
--
-- For each implementation of generic function, add call to generic function.
--
--    implementation of IEq for Int (eq(x,y))
--    var $f$Int$ x : (Int -> Int);
--
--    func $neq$Int$ (x,y) return _$neq$($IEq$Int$,x,y)
--    func $f$Int$ (x) return _$f$($IEq$Int,x)

addGCallBody (SVarSG z id (GCall clss itpc has) (tp@(T.TFunc ft inp out),cs) Nothing p) =
  SVarSG z (dols [id,T.showC itpc]) (GCall clss itpc has) (tp,cs) (Just (EFunc z (tp,Cs.cz) par_dcl bdy)) p where
    bdy = SRet z (ECall z (EVar z id') par_call) where
            id' = if has then
                    '_' : dols [id,T.showC itpc]
                  else
                    '_' : dol id

    par_dcl  = listToExp $ map (EVar z) $ fpar inp
    par_call = listToExp $ map (EVar z) $ dicts ++ fpar inp where
                dicts = map (\cls -> dols [cls,T.showC itpc]) clss

    fpar inp = map dol $ map show $ lns $ len $ T.toTTuple inp where
                len (T.TTuple l) = length l
                lns n = take n lns' where
                          lns' = 1 : map (+1) lns'


addGCallBody p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- For each existing implementation (interface or implementation), insert dict
-- parameters for all interface methods.
--
--    interface  IEq         (...,neq(x,y))
--    implementation of IEq for Int (...,eq(x,y))
--
--    func _$neq$ ($dict,x,y)
--    func _$eq$Int$ ($dict,x,y)

addGenDict :: Stmt -> Stmt

addGenDict (SVarSG z id (GImp ins xxx clss) (T.TFunc ft1 inp1 out1,cs1)
              (Just (EFunc z2 (T.TFunc ft2 inp2 out2,cs2) par2 p2))
              p) =
  SVarSG z id (GImp ins xxx clss) (T.TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (T.TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = foldr (\cls -> T.insTTuple (T.TData False [dol cls] [])) (T.toTTuple inp1) clss
    inp2' = foldr (\cls -> T.insTTuple (T.TData False [dol cls] [])) (T.toTTuple inp2) clss
    par2' = foldr (\cls -> insETuple (EVar z $ dols ["dict",cls]))   (toETuple par2)   clss

addGenDict p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Remove contraint/inst from the program (split actual dcls/impls from their
-- abstract prototypes).
--    contraint IEq        (eq,neq)
--    implementation  IEq for Int(eq,neq)
--
--    contraint IEq        (eq,neq) ; eq ; neq
--    implementation  IEq for Int(eq,neq) ; eq ; neq
--
-- For each implementation, add its dictionary.
-- First the dict declaration, then the implementation body, then the dict assignment.
--
--    implementation of IEq for Int (eq(x,y))
--
--    var $IEq$Int$ : $IEq$
--    ... // body
--    $IEq$Int$ = $IEq$(_$eq$Int$, _$neq$Int$)

inlClassInst :: Stmt -> Stmt
inlClassInst (SClassS z cls                 cs  ifc p) = SClassS z cls                 cs  ifc $ inlCI p ifc
inlClassInst (SInstSC z (cls:sups,ifc,gens) tpc imp p) = SInstSC z (cls:sups,ifc,gens) tpc imp $ inlCI (addDictIni p) (addDictDcl imp)
  where
    dict = dols [cls,T.showC tpc]
    addDictDcl imp = SVarSG z dict GNone (T.TData False [dol cls] [],Cs.cz) Nothing imp
    addDictIni p   = SSeq z (SSet z True False (EVar z dict) cons) p
                     where
                      toEVar :: (Bool,ID_Var) -> Exp
                      toEVar (True,  id) = EVar z ('_' : dol id)
                      toEVar (False, id) = EVar z ('_' : dols [id,T.showC tpc])

                      isDcl :: ID_Var -> (Bool,ID_Var)
                      isDcl id = (f id, id) where
                                  f :: ID_Var -> Bool
                                  f id = elem id $
                                          Set.difference (Set.fromList $ map toName $ toGDcls ifc)
                                                         (Set.fromList $ map toName $ toGDcls imp)

                      cons = case map toEVar $ map isDcl $ map toName $ toGDcls ifc of
                              [] -> ECons z [dol cls]
                              x  -> ECall z (ECons z [dol cls]) $ listToExp x

inlClassInst p = p

-- skip Instance GCls to prevent multiple declarations
inlCI p (SVarSG _ _ GIns _ _ (SNop _)) = p
inlCI p (SVarSG _ _ GIns _ _ q)        = inlCI p q

inlCI p (SVarSG z id gen tpc ini (SNop _)) = SVarSG z id gen tpc ini p
inlCI p (SVarSG z id gen tpc ini q)        = SVarSG z id gen tpc ini (inlCI p q)
inlCI p (SNop z)                           = p
--inlCI _ p q = error $ show q


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Declare an associated dictionay for each interface.
--
-- Each interface (IEq(eq,neq)) has an associated "dict" (_IEq(eq,neq))
-- (actually a static struct) in which each field (_IEq.eq) corresponds to a
-- method of the same name in the interface (IEq.eq):
--    contraint IEq(eq,neq)
--
--    data      $IEq(eq,neq)
--    contraint IEq(eq,neq)

dclClassDicts :: Stmt -> Stmt

dclClassDicts s@(SClassS z cls cs ifc _) = SDataS z (T.TData False [dol cls] []) (Just pars) tps Cs.cz False s
  where
    [(_,sups)] = cs
    dcls = toGDcls ifc
    pars = map f dcls where
            f (SVarSG _ id (GCls def) _ _ _) = id
    tps  = T.listToType (map f dcls) where
            f (SVarSG _ _ (GCls def) (T.TFunc ft inp out,_) _ _) =
              T.TFunc ft inp' out where
                inp' = foldr (\cls -> T.insTTuple (T.TData False [dol cls] [])) (T.toTTuple inp) (cls:sups)

dclClassDicts p = p
