module Ceu.Grammar.Full.Compile.Class where

import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)
import Data.List  (find)

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Ann         (Ann)
import Ceu.Grammar.Basic       (Gen(..))
import Ceu.Grammar.Type        (TypeC, show', sort', Type(..), FuncType(..), toTTuple, insTTuple, instantiate, listToType)
import Ceu.Grammar.Full.Full

idtp id tp = dollar $ id ++ "$" ++ show' tp

toGDcls :: Stmt -> [Stmt]
toGDcls (SClassS _ _ _ ifc _) = f ifc where
  f :: Stmt -> [Stmt]
  f s@(SVarSG _ _ GDcl _ _ p) = s : f p
  f s@(SVarSG _ _ _    _ _ p) = f p
  f   (SNop   _)        = []

-------------------------------------------------------------------------------

-- Remove contraint/inst from the program (split actual dcls/impls from their
-- abstract prototypes).
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--
--    contraint IEq        (eq,neq) ; eq ; neq
--    instance  IEq for Int(eq,neq) ; eq ; neq

inlClassInst :: Stmt -> Stmt
inlClassInst (SClassS z id  cs  ifc p) = SClassS z id  cs  ifc $ inlCI p ifc
inlClassInst (SInstS  z cls tpc imp p) = SInstS  z cls tpc imp $ inlCI p imp
inlClassInst p = p

inlCI p (SVarSG z id gen tpc ini (SNop _)) = SVarSG z id gen tpc ini p
inlCI p (SVarSG z id gen tpc ini q)        = SVarSG z id gen tpc ini (inlCI p q)
inlCI p (SNop z)                           = p
inlCI p q = error $ show q

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Insert constraint in each nested method in outer contraint/instance.
--
--    contraint IEq (eq,neq)
--
--    contraint IEq (eq where a is IEq,neq where a is IEq)

addClassCs :: Stmt -> Stmt

addClassCs (SClassS z cls cs ifc p) =
   case Cs.toList cs of
    [(var,_)]  -> SClassS z cls cs ifc' p where
                    ifc' = map_stmt (id2, Prelude.id, f) [] ifc
                    f (tp,cs) = (tp, Cs.insert (var,cls) cs)
    otherwise  -> error "TODO: multiple vars"

addClassCs p = p

-------------------------------------------------------------------------------

-- Set type of generic var.
--
--    contraint IEq        (eq,neq)
--    instance  IEq for Int(eq,neq)
--    func f : (a -> Int) where a is IEq
--
--    contraint IEq        (eq/GDcl, neq/GClass)
--    instance  IEq for Int(eq/GInst,  neq/GInstc)
--    func f/GFunc

setGen :: Stmt -> Stmt
setGen (SClassS z cls cs ifc p) = SClassS z cls cs (f ifc) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc Nothing    p) = SVarSG z id GDcl tpc Nothing $
                                        f p
    f (SVarS z id tpc (Just ini) p) = SVarSG z id GDcl tpc Nothing $
                                        SVarSG z ('_':dollar id) GGen tpc (Just ini) $
                                          f p
    f s@(SNop _) = s
setGen (SInstS z cls tpc@(itp,_) imp p) = SInstS z cls tpc (f imp) p
  where
    f :: Stmt -> Stmt
    f (SVarS z id tpc (Just ini) p) = SVarSG z ('_':idtp id itp) GOne tpc (Just ini) $
                                        SVarSG z (idtp id itp) GCall tpc Nothing $
                                          f p
    f s@(SNop _) = s
setGen p = p

setGen' :: Stmt -> Stmt
setGen' (SVarS z id tpc@(_,cs) ini p) | Map.null cs = SVarSG z id GNone tpc ini p
                                      | otherwise   = SVarSG z id GDcl tpc Nothing $
                                                        --SVarSG z ('_':idtp id itp) GRaw tpc ini $
                                                        p
setGen' p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

withEnvS :: [Stmt] -> Stmt -> Stmt

withEnvS env s@(SClassS z id  cs   ifc       p) = SClassS z id  cs  (withEnvS (s:env) ifc) (withEnvS (s:env) p)
withEnvS env s@(SInstS  z cls tpc  imp       p) = SInstS  z cls tpc (withEnvS (s:env) imp) (withEnvS (s:env) p)
withEnvS env   (SDataS  z tp  nms  st cs abs p) = SDataS  z tp  nms st cs abs              (withEnvS env p)
withEnvS env   (SMatch  z ini chk  exp cses)    = SMatch  z ini chk (withEnvE env exp) (map f cses) where
                                                    f (ds,pt,st) = (withEnvS env ds, withEnvE env pt, withEnvS env st)
withEnvS env   (SIf     z exp p1 p2)            = SIf     z (withEnvE env exp) (withEnvS env p1) (withEnvS env p2)
withEnvS env   (SSeq    z p1 p2)                = SSeq    z (withEnvS env p1) (withEnvS env p2)
withEnvS env   (SLoop   z p)                    = SLoop   z (withEnvS env p)
withEnvS env   (SVarSG  z id  GGen tpc (Just ini) p) = SVarSG z id GGen tpc (Just $ insGGenWrappers env $ withEnvE env ini) (withEnvS env p)
withEnvS env   (SVarSG  z id  gen  tpc ini        p) = SVarSG z id gen  tpc (fmap (withEnvE env) ini) (withEnvS env p)
withEnvS env   p                               = p

withEnvE :: [Stmt] -> Exp -> Exp
withEnvE env (ETuple z es)       = ETuple z (map (withEnvE env) es)
withEnvE env (EFunc  z tp ps bd) = EFunc  z tp (withEnvE env ps) (withEnvS env bd)
withEnvE env (ECall  z e1 e2)    = ECall  z (withEnvE env e1) (withEnvE env e2)
withEnvE env exp                 = exp

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

addGGenWrappers :: [Stmt] -> Exp -> Exp

addGGenWrappers env (EFunc z tpc@(tp,cs) par p) = EFunc z tpc par p' where
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
      f (SVarSG _ id GDcl (TFunc _ inp _,_) _ _) =
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

-- Unite all protos from Class/Inst.
--
--    constraint  IEq         (eq,neq)
--    instance of IEq for Int (eq)
--
--    instance of IEq for Int (eq(True),neq(False))

addInstMissing :: [Stmt] -> Stmt -> Stmt

addInstMissing env (SInstS z cls tpc@(tp,_) pts bdy) =
  SInstS z cls tpc pts' bdy where
    pts' = case find f env of
            Just (SClassS _ _ _ x _) -> Map.union pts $ Map.map noIni $ Map.difference x pts where
                                          noIni (z,id,tpc,_) = (z,id,tpc,False)
            --_ -> error $ show (cls, env)
           where
            f (SClassS _ cls' _ _ _) = (cls == cls')
            f _                      = False

addInstMissing _ p = p

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- For each existing implementation (constraint or instance), insert dict
-- parameters for all constraint methods.
--
--    constraint  IEq         (...,neq(x,y))
--    instance of IEq for Int (...,eq(x,y))
--
--    func _$neq$ ($dict,x,y)
--    func _$eq$Int$ ($dict,x,y)

addGGenDict :: Stmt -> Stmt

addGGenDict (SVarSG z id GGen (TFunc ft1 inp1 out1,cs1)
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

addGGenDict p = p

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

{-
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
--    func $f$Bool$ (x)         // wrapper to call _$f$ with $IEq$Bool$
--    ...

dupRenImpls :: [Stmt] -> Stmt -> Stmt

dupRenImpls _ (SVarS z id gen@(GClass _ _ _) tpc@(tp,_) ini p) =
  SVarS z id gen tpc Nothing $
    SVarS z ('_':dollar id) gen tpc ini $
      p

dupRenImpls _ (SVarS z id gen@(GInst _ itp) tpc' ini p) =
  SVarS z (idtp id itp) gen tpc' ini $
    SVarS z ('_':idtp id itp) gen tpc' ini $
      p

dupRenImpls env (SVarS z id gen@(GFunc [] []) tpc@(tp,cs) ini p) =
  SVarS z id gen tpc Nothing $
    SVarS z ('_':dollar id) (GFunc stmts []) tpc (fmap remCtrs ini) $
      foldr f p $ zip stmtss itpss
  where
    -- remove constraints since we already receive the actual $dict
    remCtrs :: Exp -> Exp
    remCtrs e = map_exp' (f2 Prelude.id, Prelude.id, (\(tp,_) -> (tp,Cs.cz))) e

    ---------------------------------------------------------------------------

    -- one F for each instance

    f :: ([Stmt],[Type]) -> Stmt -> Stmt
    f (x,[itp]) p = SVarS z (idtp id itp) (GFunc x [itp]) (tp',Cs.cz) Nothing p where
                        tp' = instantiate [("a",itp)] tp

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

dupRenImpls _ p = p

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
-- For each instance of generic function, add call to generic function.
--
--    instance of IEq for Int (eq(x,y))
--    var $f$Int$ x : (Int -> Int);
--
--    func $neq$Int$ (x,y) return _$neq$($IEq$Int$,x,y)
--    func $f$Int$   (x)   return _$f$($IEq$Int,x)

addInstances :: Stmt -> Stmt

addInstances (SInstS z cls tpc@(tp,_) pts (SVarS z2 id2 gen2 tp2 Nothing bdy)) =
  SInstS z cls tpc pts (SVarS z2 id2 gen2 tp2 Nothing bdy') where
    bdy' = foldr ($) bdy $ map g $ Map.elems $ Map.filter f pts where
            f (_,_,_,ini) = not ini   -- only methods w/o implementation

            g :: Proto -> (Stmt -> Stmt)
            g (z2,id2,tpc2@(tp2,_),False) = SVarS z2 (idtp id2 tp) gen2 tpc2' (Just (EFunc z2 tpc2' par_dcl p)) where
              tp2' = instantiate [("a",tp)] tp2  -- TODO: a is fixed
              (TFunc _ inp2' _) = tp2'
              tpc2' = (tp2',Cs.cz)

              p = SRet z2 (ECall z2 (EVar z2 ('_':dollar id2)) par_call)

              par_dcl  = listToExp $ map (EVar z2) $ fpar inp2'
              par_call = listToExp $ map (EVar z2) $ (("$"++cls++"$"++show' tp++"$") :) $ fpar inp2'

addInstances (SVarS z ('$':id) gen@(GFunc [SClassS _ cls _ _ _] [tp]) tpc@(TFunc _ inp _,_) Nothing p) =
   SVarS z ('$':id) gen tpc (Just (EFunc z tpc par_dcl bdy)) p where
    par_dcl  = listToExp $ map (EVar z) $ fpar inp
    par_call = listToExp $ map (EVar z) $ (id :) $ fpar inp where
                id = dollar $ cls++"$"++show' tp
    bdy  = SRet z (ECall z (EVar z id') par_call) where
            id' = '_' : dollar (head $ splitOn '$' id)

addInstances p = p

fpar inp = map ('$':) $ map show $ lns $ len $ toTTuple inp where
            len (TTuple l) = length l
            lns n = take n lns' where
                      lns' = 1 : map (+1) lns'
-}
