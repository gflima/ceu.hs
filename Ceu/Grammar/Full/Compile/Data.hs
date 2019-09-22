module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)
import Data.Bool (bool)

import Ceu.Trace
import Ceu.Grammar.Ann
import Ceu.Grammar.Globals
import Ceu.Grammar.Type               (Type(..),TypeC,instantiate,getSuper,hier2str,FuncType(..))
import Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Basic              (Gen(..))
import Ceu.Grammar.Full.Full

-- Instantiates variable declarations of TData with their complete types:
--
-- data Pair with (Int,Int)
--    var p : Pair
-- becomes
--    var p : Pair (Int,Int)
--
-- data Pair with (a,b,Bool)
--    var p : Pair of (X,Y)
-- becomes
--    var p : Pair (X,Y,Bool)

-------------------------------------------------------------------------------

expHier :: [Stmt] -> Stmt -> Stmt
expHier ds (SClassS  z id  cs ifc p) = SClassS z id  cs ifc (expHier ds p)
expHier ds (SInstS   z cls tp imp p) = SInstS  z cls tp imp (expHier ds p)
expHier ds (SDataS   z tp nms st cs abs p) = SDataS z tp' nms' st' cs' abs (expHier (d':ds) p)
                                             where
                                              (tp',nms',st',cs') = fdata ds (tp,nms,st,cs)
                                              d' = SDataS z tp' nms' st' cs' abs p
expHier ds (SVarSG   z var gen tp ini p) = SVarSG  z var gen tp (fmap (expr ds) ini) (expHier ds p)
expHier ds (SMatch   z ini chk exp cses) = SMatch  z ini chk (expr ds exp)
                                             (map (\(xs,pt,st) -> (expHier ds xs, expr ds pt, expHier ds st)) cses)
expHier ds (SCall    z exp)          = SCall    z (expr ds exp)
expHier ds (SSeq     z p1 p2)        = SSeq     z (expHier ds p1) (expHier ds p2)
expHier ds (SLoop    z p)            = SLoop    z (expHier ds p)
expHier ds (SRet     z exp)          = SRet     z (expr ds exp)
expHier _  p                         = p

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> Exp
expr ds (ETuple z es)            = ETuple z (map (expr ds) es)
expr ds (ECall  z e1 e2)         = ECall  z (expr ds e1) (expr ds e2)
expr ds (EFunc  z tp par imp)    = EFunc  z tp par (expHier ds imp)
expr _  e                        = e

-------------------------------------------------------------------------------

fdata :: [Stmt] -> (Type, Maybe [String], Type, Cs.Map) -> (Type, Maybe [String], Type, Cs.Map)
fdata ds (tp@(TData False id ofs), nms, st, cs) = case getSuper id of
  Nothing  -> (tp,nms,st,cs)
  Just sup -> case find (\(SDataS _ (TData False id' _) _ _ _ _ _) -> id'==sup) ds of
                Nothing -> (tp,nms,st,cs)
                Just (SDataS _ (TData False _ ofs') nms' st' cs' _ _) ->
                  case any (\v2 -> elem v2 ofs) ofs' of
                    True  -> error $ "TODO: repeated variables"
                    False -> (TData False id (ofs' ++ ofs), ret, cat st' st, Cs.union cs' cs)
                             where
                              ret = case (nms',nms) of
                                      (Nothing,Nothing) -> Nothing
                                      (Just l, Nothing) -> error "TODO"
                                      (Nothing,Just l)  -> error "TODO"
                                      (Just l1,Just l2) -> Just $ l1 ++ l2
  where
    cat :: Type -> Type -> Type
    cat TUnit       tp          = tp
    cat tp          TUnit       = tp
    cat (TTuple l1) (TTuple l2) = TTuple $ l1 ++ l2
    cat (TTuple l1) tp          = TTuple $ l1 ++ [tp]
    cat tp          (TTuple l2) = TTuple $ tp :  l2
    cat tp1         tp2         = TTuple $ [tp1,tp2]

-------------------------------------------------------------------------------

addAccs :: Stmt -> Stmt
addAccs (SDataS  z tp nms st cs abs p) = SDataS z tp nms st cs abs (faccs z nms (tp,st,cs) p)
addAccs p = p

-------------------------------------------------------------------------------

-- accessors
-- data X with (...,Int,...)
-- X_2 : (X -> Int)

faccs :: Ann -> Maybe [ID_Var] -> (Type,Type,Cs.Map) -> Stmt -> Stmt
faccs z nms (tpD@(TData False hr _),st,cs) p = accs where
  (accs,_) = foldr f (p, len st) (g st)

  hr_str = hier2str hr

  g :: Type -> [Type]
  g (TTuple l) = l
  g TUnit      = []
  g tp         = [tp]

  len (TTuple l) = length l
  len _          = 1

  f :: Type -> (Stmt,Int) -> (Stmt,Int)
  f tp (p,idx) = (SVarSG z id GNone (TFunc FuncGlobal tpD tp,cs) (Just body) (nm p), idx-1)
                 where
                  id = hr_str ++ "._" ++ show idx

                  body = EFunc z (TFunc FuncGlobal tpD tp,cs) (EAny z)
                          (SVarSG z "_ret" GNone (tp,cs) Nothing -- (Just $ EArg z) (SRet z (EVar z "_ret")))
                            (SMatch z True False (EArg z) [(SNop z, ret, SRet z (EVar z "_ret"))]))

                  ret  = ECall z (ECons z hr) (bool (ETuple z repl) (repl!!0) (len st == 1))
                  repl = take (idx-1) anys ++ [EVar z "_ret"] ++ drop idx anys
                  anys = replicate (len st) (EAny z)

                  nm p = case nms of
                          Nothing -> p
                          Just l  -> SVarSG z idm GNone (TFunc FuncGlobal tpD tp,cs) (Just body) p
                                     where
                                      idm = hr_str ++ "." ++ (l!!(idx-1))
                                      body = EFunc z (TFunc FuncGlobal tpD tp,cs) (EAny z)
                                                     (SRet z (ECall z (EVar z id) (EArg z)))
