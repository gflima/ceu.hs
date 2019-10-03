module Ceu.Grammar.Full.Compile.Class where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)
import Data.List  (find)

import Ceu.Trace
import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann, toError)
import qualified Ceu.Grammar.Type as T
import Ceu.Grammar.Full.Full

idtpc id tpc = dollar $ id ++ "$" ++ T.showC tpc

toGDcls :: Stmt -> [Stmt]
toGDcls (SClassS _ _ _ ifc _) = toGDcls' ifc
toGDcls (SInstS  _ _ _ imp _) = toGDcls' imp

toGDcls' :: Stmt -> [Stmt]
toGDcls' s@(SVarSG _ _ GDcl _ _ p) = s : toGDcls' p
toGDcls' s@(SVarSG _ _ _    _ _ p) = toGDcls' p
toGDcls'   (SNop   _)              = []

toName :: Stmt -> ID_Var
toName (SVarSG _ id _ _ _ _) = id

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Insert interface in each nested method in outer contraint/implementation.
-- Do not recurse into bodies with map_stmt.
--
--    contraint IEq (eq,neq)
--    contraint IEq (eq where a is IEq,neq where a is IEq)
--
--    instance of IEq for a where a is IXx
--    func eq (x,y) : ((a,a) -> Int where a is IXx)

addClassCs :: Stmt -> Stmt

addClassCs (SClassS z cls cs ifc p) = SClassS z cls cs (f ifc) p
  where
    [(var,_)] = Cs.toList cs
    f :: Stmt -> Stmt
    f (SVarS z id tpc ini p) = SVarS z id (g tpc) ini (f p) where
                                g (tp,cs) = (tp, Cs.insert (var,cls) cs)
    f s@(SNop _) = s

addClassCs (SInstS z cls itpc@(_,cs) imp p) = SInstS z cls itpc imp' p
  where
    imp' = case Cs.toList cs of
            []        -> imp
            [(var,_)] -> f imp where
              f :: Stmt -> Stmt
              f (SVarS z id tpc ini p) = SVarS z id (g tpc) ini (f p) where
                                          g (tp,cs) = (tp, Cs.insert (var,cls) cs)
              f s@(SNop _) = s

addClassCs p = p

-------------------------------------------------------------------------------

-- Set type of generic var.
--
--    contraint IEq        (eq,neq)
--    implementation  IEq for Int(eq,neq)
--    func f : (a -> Int) where a is IEq
--
--    contraint IEq        (eq/GDcl, neq/GClass)
--    implementation  IEq for Int(eq/GInst,  neq/GInstc)
--    func f/GFunc

setGen :: Stmt -> Stmt
setGen (SClassS z cls cs ifc p) = SClassS z cls cs (f ifc) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc         Nothing    p) = SVarSG z id GDcl tpc Nothing $
                                                f p
    f (SVarS z id tpc@(tp,cs) (Just ini) p) = SVarSG z ('_':dollar id) (GGen cs) (tp,Cs.cz) (Just ini) $
                                                SVarSG z id GDcl tpc Nothing $
                                                  f p
    f s@(SNop _) = s
setGen (SInstS z cls itpc imp p) = SInstS z cls itpc (f imp) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc@(tp,_) (Just ini) p) = SVarSG z ('_':idtpc id itpc) (GOne cls) (tp,Cs.cz) (Just ini) $
                                              SVarSG z id GDcl tpc Nothing $
                                                SVarSG z id (GCall cls itpc True) (tp,Cs.cz) Nothing $
                                                  f p
    f s@(SNop _) = s
setGen p = p

setGen' :: Stmt -> Stmt
setGen' (SVarS z id tpc@(tp,cs) ini p) | Map.null cs = SVarSG z id GNone tpc ini p
                                       | otherwise   = SVarSG z ('_':dollar id) (GGen cs) (tp,Cs.cz) (remCs ini) $
                                                        SVarSG z id GDcl tpc Nothing $
                                                          p
  where
    remCs :: Maybe Exp -> Maybe Exp
    remCs (Just (EFunc z (tp,_) ps bd)) = Just (EFunc z (tp,Cs.cz) ps bd)

setGen' p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

withEnvS :: [Stmt] -> Stmt -> (Errors,Stmt)

withEnvS env s@(SClassS z id cs ifc p) = (es1++es2++es3, SClassS z id cs ifc' p') where
                                            es1        = chkClassSupsDeclared env z cs
                                            (es2,ifc') = withEnvS (s:env) ifc
                                            (es3,p')   = withEnvS (s:env) p

withEnvS env s@(SInstS z cls tpc imp p) = (es1++es2, addClassGensToInst env $ SInstS z cls tpc imp' p') where
                                            (es1,imp') = withEnvS (s:env) imp
                                            (es2,p')   = withEnvS (s:env) p

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

withEnvS env (SVarSG z id  (GGen cs) tpc (Just ini) p) =
  (es1++es2, SVarSG z id (GGen cs) tpc (Just $ addGGenWrappers cs env ini') p')
  where
    (es1,ini') = withEnvE env ini
    (es2,p')   = withEnvS env p


withEnvS env s@(SVarSG z id GDcl tpc Nothing p) =
  (es, repGGenInsts env $ SVarSG z id GDcl tpc Nothing p')
  where
    (es,p') = withEnvS (s:env) p

withEnvS env (SVarSG z id gen tpc ini p) =
  (es1++es2, SVarSG z id gen tpc ini' p')
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

chkClassSupsDeclared :: [Stmt] -> Ann -> Cs.Map -> Errors
chkClassSupsDeclared env z cs =
  case Cs.toList cs of
    [(_,sups)] -> concatMap f sups where
      f sup = case find (isClass sup) env of
        Nothing -> [toError z $ "interface '" ++ sup ++ "' is not declared"]
        Just _  -> []
      isClass id1 (SClassS _ id2 _ _ _) = traceShowX (id1,id2) (id1 == id2)
      isClass _   _                     = False
    otherwise  -> error "TODO: multiple vars"

{-
chkClassSupsDeclared :: [Stmt] -> Ann -> Cs.Map -> Errors
chkInstSupsDeclared env ... =
              -- check extends
              --  interface      (Eq  for a)
              --  implementation (Eq  for Bool)                  <-- so Bool must implement Eq
              --  interface      (Ord for a) extends (Eq for a)  <-- but Ord extends Eq
              --  implementation (Ord for Bool)                  <-- Bool implements Ord
              es1 = concatMap f sups where
                f sup = case find (isInstOf sup xxx) (concat envs) of
                  Nothing -> [toError z $ "implementation '" ++ sup ++ " for " ++
                              (T.show' itp) ++ "' is not declared"]
                  Just _  -> []
                isInstOf x y (SInst _ x' y' _ _) = (x'==x && y' `T.isSupOfC` y)
                isInstOf _ _ _                   = False
-}

-------------------------------------------------------------------------------

addClassGensToInst :: [Stmt] -> Stmt -> Stmt
addClassGensToInst env s@(SInstS z cls tpc imp p) = SInstSC z (cls,ifc,gens) tpc imp p
  where
    ifc = case find f env of                  -- TODO: more css
            Just (SClassS _ _ _ ifc _) -> ifc -- TODO: Nothing
            where
              f (SClassS _ id _ _ _) = id == cls
              f _ = False
    gens = filter f env where
            f (SVarSG _ id GDcl (_,cs) _ _) = (cls == cls') where
                                                cls' = case Cs.toList cs of
                                                  [(_,[cls])] -> cls
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

addGGenWrappers :: Cs.Map -> [Stmt] -> Exp -> Exp

addGGenWrappers cs env (EFunc z tpc par p) = EFunc z tpc par p' where
  p'  = cls2wrappers p cls
  cls = case Cs.toList cs of
          [(_,[cls])] -> case find f env of     -- TODO: more css
                          Just s -> s           -- TODO: Nothing
                         where
                          f (SClassS _ id _ _ _) = id == cls
                          f _ = False

  cls2wrappers :: Stmt -> Stmt -> Stmt
  cls2wrappers p s@(SClassS _ cls _ ifc _) =
    foldr ($) p (map f $ toGDcls s) where
      f :: Stmt -> (Stmt -> Stmt)
      f (SVarSG _ id GDcl (tp@(T.TFunc _ inp _),_) _ _) =
        SVarSG z (dollar id) GNone (tp,Cs.cz) $          -- remove cs
          Just (EFunc z (tp,Cs.cz) (expand inp) body)
        where
          body = SRet z (ECall z
                        (ECall z (EField z [dollar cls] id) (EVar z "$dict"))
                        (insETuple (EVar z "$dict") (toETuple $ expand inp)))

      -- expand inputs:
      -- ($1,$2) = EArg
      -- call f ($dict,$1,$2)
      expand (T.TTuple l) = ETuple z $
                              map (\v->EVar z v) $
                                take (length l) $
                                  map (\v->'$':show v) $
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
repGGenInsts env (SVarSG z id GDcl tpc@(tp,cs) Nothing p) =
  SVarSG z id GDcl tpc Nothing $
    foldr f p $ zip stmtss itpcss
  where
    -- one F for each implementation

    f :: ([Stmt],[T.TypeC]) -> Stmt -> Stmt
    f ([SClassS _ cls _ _ _],[itpc]) p =
      SVarSG z id (GCall cls itpc False) tpc' Nothing p where
        tpc' = T.instantiateC [("a",itpc)] tp

    idss :: [[ID_Class]]
    idss = map Set.toList $ Map.elems cs

    stmtss :: [[Stmt]]
    stmtss = map (map getCls) $ map Set.toList $ Map.elems cs where
              getCls cls = case find f env of
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
    combos' lvl env clss = combos insts where
      insts :: [[T.TypeC]]
      insts = map h clss
        where
          h :: [ID_Class] -> [T.TypeC]
          h [cls] = concatMap h $ map g $ filter f env where
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
              tpcss = combos' (lvl-1) env (map Set.toList $ Map.elems cs)
              insts :: [T.TypeC]
              insts = map (flip T.instantiateC tp) $ map (zip (Map.keys cs)) tpcss

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Add missing interface methods and generic functions to implementation.
--
--    interface  IEq         (eq,neq)
--    func f (x) where x is IEq
--    implementation of IEq for Int (eq)
--
--    implementation of IEq for Int (eq(Just),neq(Nothing),f(Nothing))

addInstGCalls :: Stmt -> Stmt

addInstGCalls (SInstSC z (cls,ifc,gens) itpc imp p) =
  SInstSC z (cls,ifc,gens) itpc imp' p where
    dif  = Set.difference (Set.fromList $ map toName $ toGDcls' ifc) (Set.fromList $ map toName $ toGDcls' imp)

    all  = gens ++ filter f (toGDcls' ifc) where
            f (SVarSG _ id _ _ _ _) = elem id dif

    imp' = foldr ($) imp (map f all) where
            f :: Stmt -> (Stmt -> Stmt)
            f (SNop _) = Prelude.id
            f (SVarSG z2 id2 gen2 tpc2@(tp2,_) _ _) =
              SVarSG z2 id2 (GCall cls itpc False) tpc2' Nothing where
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

addGCallBody (SVarSG z id (GCall cls itpc has) (tp@(T.TFunc ft inp out),cs) Nothing p) =
  SVarSG z (idtpc id itpc) (GCall cls itpc has) (tp,Cs.cz) (Just (EFunc z (tp,Cs.cz) par_dcl bdy)) p where
    bdy = SRet z (ECall z (EVar z id') par_call) where
            id' = if has then
                    '_' : idtpc id itpc
                  else
                    '_' : dollar id

    par_dcl  = listToExp $ map (EVar z) $ fpar inp
    par_call = listToExp $ map (EVar z) $ (("$"++cls++"$"++T.showC itpc++"$") :) $ fpar inp

    fpar inp = map ('$':) $ map show $ lns $ len $ T.toTTuple inp where
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

addGenDict (SVarSG z id (GGen cs) (T.TFunc ft1 inp1 out1,cs1)
              (Just (EFunc z2 (T.TFunc ft2 inp2 out2,cs2) par2 p2))
              p) =
  SVarSG z id (GGen cs) (T.TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (T.TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = T.insTTuple (T.TData False [dollar cls] []) (T.toTTuple inp1)
    inp2' = T.insTTuple (T.TData False [dollar cls] []) (T.toTTuple inp2)
    par2' = insETuple (EVar z "$dict") (toETuple par2)
    [(_,[cls])] = Cs.toList cs -- TODO: more css

addGenDict (SVarSG z id (GOne cls) (T.TFunc ft1 inp1 out1,cs1)
              (Just (EFunc z2 (T.TFunc ft2 inp2 out2,cs2) par2 p2))
              p) =
  SVarSG z id (GOne cls) (T.TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (T.TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = T.insTTuple (T.TData False [dollar cls] []) (T.toTTuple inp1)
    inp2' = T.insTTuple (T.TData False [dollar cls] []) (T.toTTuple inp2)
    par2' = insETuple (EVar z "$dict") (toETuple par2)

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
inlClassInst (SClassS z id             cs  ifc p) = SClassS z id             cs  ifc $ inlCI False p ifc
inlClassInst (SInstSC z (cls,ifc,gens) tpc imp p) = SInstSC z (cls,ifc,gens) tpc imp $ inlCI True  (addDictIni p) (addDictDcl imp)
  where
    dict = dollar $ cls ++ "$" ++ T.showC tpc
    addDictDcl imp = SVarSG z dict GNone (T.TData False [dollar cls] [],Cs.cz) Nothing imp
    addDictIni p   = SSeq z
                      (SSet z True False
                        (EVar z dict)
                        (ECall z (ECons z [dollar cls]) (listToExp $ map toEVar $ map isDcl $ map toName $ toGDcls' ifc)))
                      p
                     where
                      toEVar :: (Bool,ID_Var) -> Exp
                      toEVar (True,  id) = EVar z ('_' : dollar id)
                      toEVar (False, id) = EVar z ('_' : dollar (id++"$"++T.showC tpc))

                      isDcl :: ID_Var -> (Bool,ID_Var)
                      isDcl id = (f id, id) where
                                  f :: ID_Var -> Bool
                                  f id = elem id $
                                          Set.difference (Set.fromList $ map toName $ toGDcls' ifc)
                                                         (Set.fromList $ map toName $ toGDcls' imp)

inlClassInst p = p

-- skip Instance GDcl to prevent multiple declarations
inlCI True p (SVarSG _ _ GDcl _ _ (SNop _)) = p
inlCI True p (SVarSG _ _ GDcl _ _ q)        = inlCI True p q

inlCI _ p (SVarSG z id gen tpc ini (SNop _)) = SVarSG z id gen tpc ini p
inlCI b p (SVarSG z id gen tpc ini q)        = SVarSG z id gen tpc ini (inlCI b p q)
inlCI _ p (SNop z)                           = p
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

dclClassDicts cls@(SClassS z id _ _ _) =
  SDataS z (T.TData False [dollar id] []) (Just pars) tps Cs.cz False cls
  where
    dcls = toGDcls cls
    pars = map f dcls where
            f (SVarSG _ id GDcl _ _ _) = id
    tps  = T.listToType (map f dcls) where
            f (SVarSG _ _ GDcl (T.TFunc ft inp out,_) _ _) =
              T.TFunc ft inp' out where
                inp' = T.insTTuple (T.TData False [dollar id] []) (T.toTTuple inp)

dclClassDicts p = p
