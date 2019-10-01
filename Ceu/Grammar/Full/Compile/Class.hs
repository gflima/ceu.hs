module Ceu.Grammar.Full.Compile.Class where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)
import Data.List  (find)

import Ceu.Trace
import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Type        (TypeC, show', showC, sort', Type(..), FuncType(..), toTTuple, insTTuple, instantiateC, instantiate, listToType)
import Ceu.Grammar.Full.Full

idtpc id tpc = dollar $ id ++ "$" ++ showC tpc

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
--
--    contraint IEq (eq,neq)
--
--    contraint IEq (eq where a is IEq,neq where a is IEq)

addClassCs :: Stmt -> Stmt

addClassCs (SClassS z cls cs ifc p) = SClassS z cls cs ifc' p
  where
    ifc' = case Cs.toList cs of
            [(var,_)] -> map_stmt (id2, Prelude.id, f) [] ifc where
                          f (tp,cs) = (tp, Cs.insert (var,cls) cs)
            otherwise -> error "TODO: multiple vars"

addClassCs s@(SInstS z cls tpc@(_,cs) imp p) = SInstS z cls tpc imp' p
  where
    imp' = case Cs.toList cs of
            []        -> imp
            [(var,_)] -> map_stmt (id2, Prelude.id, f) [] imp where
                          f (tp,cs) = (tp, Cs.insert (var,cls) cs)
            otherwise -> error "TODO: multiple vars"
{-
-}

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
    f (SVarS z id tpc Nothing    p) = SVarSG z id GDcl tpc Nothing $
                                        f p
    f (SVarS z id tpc (Just ini) p) = SVarSG z ('_':dollar id) GGen tpc (Just ini) $
                                        SVarSG z id GDcl tpc Nothing $
                                          f p
    f s@(SNop _) = s
setGen (SInstS z cls itpc imp p) = SInstS z cls itpc (f imp) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc (Just ini) p) = SVarSG z ('_':idtpc id itpc) (GOne cls) tpc (Just ini) $
                                        SVarSG z id GDcl tpc Nothing $
                                          SVarSG z id (GCall cls itpc True) tpc Nothing $
                                            f p
    f s@(SNop _) = s
setGen p = p

setGen' :: Stmt -> Stmt
setGen' (SVarS z id tpc@(_,cs) ini p) | Map.null cs = SVarSG z id GNone tpc ini p
                                      | otherwise   = SVarSG z ('_':dollar id) GGen tpc ini $
                                                        SVarSG z id GDcl tpc Nothing $
                                                          p
setGen' p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

withEnvS :: [Stmt] -> Stmt -> Stmt

withEnvS env s@(SClassS z id  cs   ifc       p) = SClassS z id  cs  (withEnvS (s:env) ifc) (withEnvS (s:env) p)
withEnvS env s@(SInstS  z cls tpc  imp       p) = addClassGensToInst env $ SInstS z cls tpc (withEnvS (s:env) imp) (withEnvS (s:env) p)
withEnvS env   (SDataS  z tp  nms  st cs abs p) = SDataS  z tp  nms st cs abs              (withEnvS env p)
withEnvS env   (SMatch  z ini chk  exp cses)    = SMatch  z ini chk (withEnvE env exp) (map f cses) where
                                                    f (ds,pt,st) = (withEnvS env ds, withEnvE env pt, withEnvS env st)
withEnvS env   (SIf     z exp p1 p2)            = SIf     z (withEnvE env exp) (withEnvS env p1) (withEnvS env p2)
withEnvS env   (SSeq    z p1 p2)                = SSeq    z (withEnvS env p1) (withEnvS env p2)
withEnvS env   (SLoop   z p)                    = SLoop   z (withEnvS env p)
withEnvS env   (SVarSG  z id  GGen tpc (Just ini) p) =
  SVarSG z id GGen tpc (Just $ addGGenWrappers env $ withEnvE env ini) (withEnvS env p)
withEnvS env s@(SVarSG  z id  GDcl tpc Nothing    p) =
  repGGenInsts env $ SVarSG z id GDcl tpc Nothing (withEnvS (s:env) p)
withEnvS env   (SVarSG  z id  gen  tpc ini        p) =
  SVarSG z id gen  tpc (fmap (withEnvE env) ini) (withEnvS env p)
withEnvS env   p                               = p

withEnvE :: [Stmt] -> Exp -> Exp
withEnvE env (ETuple z es)       = ETuple z (map (withEnvE env) es)
withEnvE env (EFunc  z tp ps bd) = EFunc  z tp (withEnvE env ps) (withEnvS env bd)
withEnvE env (ECall  z e1 e2)    = ECall  z (withEnvE env e1) (withEnvE env e2)
withEnvE env exp                 = exp

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

addGGenWrappers :: [Stmt] -> Exp -> Exp

addGGenWrappers env (EFunc z tpc@(_,cs) par p) = EFunc z tpc par p' where
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
      f (SVarSG _ id GDcl (tp@(TFunc _ inp _),_) _ _) =
        SVarSG z (dollar id) GNone (tp,Cs.cz) $          -- remove cs
          Just (EFunc z (tp,Cs.cz) (expand inp) body)
        where
          body = SRet z (ECall z
                        (ECall z (EField z [dollar cls] id) (EVar z "$dict"))
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
    -- remove interfaces since we already receive the actual $dict
    remCtrs :: Exp -> Exp
    remCtrs e = map_exp' (f2 Prelude.id, Prelude.id, (\(tp,_) -> (tp,Cs.cz))) e

    ---------------------------------------------------------------------------

    -- one F for each implementation

    f :: ([Stmt],[TypeC]) -> Stmt -> Stmt
    f ([SClassS _ cls _ _ _],[itpc]) p =
      SVarSG z id (GCall cls itpc False) tpc' Nothing p where
        tpc' = instantiateC [("a",itpc)] tp

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

    itpcss :: [[TypeC]]
    --itpcss = sort' $ combos' 1 env idss
    itpcss = combos' 1 env idss

    -- [ [Ia], [Ib], ... ]
    -- [ [A1,A2,...], [B1,B2,...], ... ]
    -- [ [A1,B1,...], [A1,B2,...], ... ]
    combos' :: Int -> [Stmt] -> [[ID_Class]] -> [[TypeC]]
    combos' lvl env clss = combos insts where
      insts :: [[TypeC]]
      insts = map h clss
        where
          h :: [ID_Class] -> [TypeC]
          h [cls] = concatMap h $ map g $ filter f env where
            f :: Stmt -> Bool
            f (SInstS _ cls' (_,cs') _ _) = (cls == cls') && (lvl>0 || null cs')
            f _                           = False

            g :: Stmt -> TypeC
            g (SInstS _ _ tpc _ _) = tpc  -- types to instantiate

            -- expand types with interfaces to multiple types
            -- TODO: currently refuse another level of interfaces
            -- Int    -> [Int]
            -- X of a -> [X of Int, ...]
            h :: TypeC -> [TypeC]
            h tpc@(tp,cs) = if null cs then [tpc] else insts where
              tpcss :: [[TypeC]]
              tpcss = combos' (lvl-1) env (map Set.toList $ Map.elems cs)
              insts :: [TypeC]
              insts = map (flip instantiateC tp) $ map (zip (Map.keys cs)) tpcss

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
                tpc2' = instantiateC [("a",itpc)] tp2  -- TODO: a is fixed
                (TFunc _ inp2' _, _) = tpc2'

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

addGCallBody (SVarSG z id (GCall cls itpc has) tpc@(TFunc ft inp out,cs) Nothing p) =
  SVarSG z (idtpc id itpc) (GCall cls itpc has) tpc (Just (EFunc z tpc par_dcl bdy)) p where
    bdy = SRet z (ECall z (EVar z id') par_call) where
            id' = if has then
                    '_' : idtpc id itpc
                  else
                    '_' : dollar id

    par_dcl  = listToExp $ map (EVar z) $ fpar inp
    par_call = listToExp $ map (EVar z) $ (("$"++cls++"$"++showC itpc++"$") :) $ fpar inp

    fpar inp = map ('$':) $ map show $ lns $ len $ toTTuple inp where
                len (TTuple l) = length l
                lns n = take n lns' where
                          lns' = 1 : map (+1) lns'


addGCallBody p = p

  {-
(Just (EFunc z2 tpc2' par_dcl p))
  addInstances :: Stmt -> Stmt

  addInstances (SInstS z cls tpc@(tp,_) pts (SVarS z2 id2 gen2 tp2 Nothing bdy)) =
    SInstS z cls tpc pts (SVarS z2 id2 gen2 tp2 Nothing bdy') where
      bdy' = foldr ($) bdy $ map g $ Map.elems $ Map.filter f pts where
              f (_,_,_,ini) = not ini   -- only methods w/o implementation

  addInstances (SVarS z ('$':id) gen@(GFunc [SClassS _ cls _ _ _] [tp]) tpc@(TFunc _ inp _,_) Nothing p) =
     SVarS z ('$':id) gen tpc (Just (EFunc z tpc par_dcl bdy)) p where
      par_dcl  = listToExp $ map (EVar z) $ fpar inp
      par_call = listToExp $ map (EVar z) $ (id :) $ fpar inp where
                  id = dollar $ cls++"$"++show' tp
      bdy  = SRet z (ECall z (EVar z id') par_call) where
              id' = '_' : dollar (head $ splitOn '$' id)

  addInstances p = p
  -}

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

addGenDict (SVarSG z id GGen (TFunc ft1 inp1 out1,cs1)
              (Just (EFunc z2 (TFunc ft2 inp2 out2,cs2) par2 p2))
              p) =
  SVarSG z id GGen (TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = insTTuple (TData False [dollar cls] []) (toTTuple inp1)
    inp2' = insTTuple (TData False [dollar cls] []) (toTTuple inp2)
    par2' = insETuple (EVar z "$dict") (toETuple par2)
    [(_,[cls])] = Cs.toList cs1 -- TODO: more css

addGenDict (SVarSG z id (GOne cls) (TFunc ft1 inp1 out1,cs1)
              (Just (EFunc z2 (TFunc ft2 inp2 out2,cs2) par2 p2))
              p) =
  SVarSG z id (GOne cls) (TFunc ft1 inp1' out1,cs1)
    (Just (EFunc z2 (TFunc ft2 inp2' out2,cs2) par2' p2))
    p
  where
    inp1' = insTTuple (TData False [dollar cls] []) (toTTuple inp1)
    inp2' = insTTuple (TData False [dollar cls] []) (toTTuple inp2)
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
inlClassInst (SClassS z id             cs         ifc p) = SClassS z id             cs  ifc $ inlCI False p ifc
inlClassInst (SInstSC z (cls,ifc,gens) tpc@(tp,_) imp p) = SInstSC z (cls,ifc,gens) tpc imp $ inlCI True  (addDictIni p) (addDictDcl imp)
  where
    dict = dollar $ cls ++ "$" ++ show' tp
    addDictDcl imp = SVarSG z dict GNone (TData False [dollar cls] [],Cs.cz) Nothing imp
    addDictIni p   = SSeq z
                      (SSet z True False
                        (EVar z dict)
                        (ECall z (ECons z [dollar cls]) (listToExp $ map toEVar $ map isDcl $ map toName $ toGDcls' ifc)))
                      p
                     where
                      toEVar :: (Bool,ID_Var) -> Exp
                      toEVar (True,  id) = EVar z ('_' : dollar id)
                      toEVar (False, id) = EVar z ('_' : dollar (id++"$"++show' tp))

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
  SDataS z (TData False [dollar id] []) (Just pars) tps Cs.cz False cls
  where
    dcls = toGDcls cls
    pars = map f dcls where
            f (SVarSG _ id GDcl _ _ _) = id
    tps  = listToType (map f dcls) where
            f (SVarSG _ _ GDcl (TFunc ft inp out,_) _ _) =
              TFunc ft inp' out where
                inp' = insTTuple (TData False [dollar id] []) (toTTuple inp)

dclClassDicts p = p
