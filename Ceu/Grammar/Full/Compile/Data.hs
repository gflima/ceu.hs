module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)
import Data.Bool (bool)

import Ceu.Grammar.Ann
import Ceu.Grammar.Globals
import Ceu.Grammar.Type               (Type(..),TypeC,instantiate,getSuper,hier2str)
import Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt [] p

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

stmt :: [Stmt] -> Stmt -> Stmt
stmt ds (SClass'' z id  cs ifc p) = SClass'' z id  cs ifc (stmt ds p)
stmt ds (SInst''  z cls tp imp p) = SInst''  z cls tp imp (stmt ds p)
stmt ds (SData''  z nms tp abs p) = SData''  z nms' tp' abs (stmt (d':ds) (faccs z nms' tp' p))
                                    where
                                      (nms',tp') = fdata ds nms tp
                                      d'         = SData'' z nms' tp' abs p
stmt ds (SVar''   z var tp p)     = SVar''   z var (fvar ds tp) (stmt ds p)
stmt ds (SMatch'  z chk exp cses) = SMatch'  z chk (expr ds exp)
                                      (map (\(xs,pt,st) -> (stmt ds xs, expr ds pt, stmt ds st)) cses)
stmt ds (SCall   z exp)           = SCall   z (expr ds exp)
stmt ds (SSeq     z p1 p2)        = SSeq     z (stmt ds p1) (stmt ds p2)
stmt ds (SLoop    z p)            = SLoop    z (stmt ds p)
stmt ds (SRet     z exp)          = SRet     z (expr ds exp)
stmt _  p                         = p

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> Exp
expr ds (ETuple z es)            = ETuple z (map (expr ds) es)
expr ds (ECall  z e1 e2)         = ECall  z (expr ds e1) (expr ds e2)
expr ds (EFunc  z env tp p)      = EFunc  z env tp (stmt ds p)
expr _  e                        = e

-------------------------------------------------------------------------------

fdata :: [Stmt] -> Maybe [String] -> TypeC -> (Maybe [String], TypeC)
fdata ds nms tp@(TData id ofs st, ctrs) = case getSuper id of
  Nothing  -> (nms,tp)
  Just sup -> case find (\(SData'' _ _ (TData id' _ _,_) _ _) -> id'==sup) ds of
                Nothing -> (nms,tp)
                Just (SData'' _ nms' (TData _ ofs' st',ctrs') _ _) ->
                  case any (\v2 -> elem v2 ofs) ofs' of
                    True  -> error $ "TODO: repeated variables"
                    False -> (ret, (TData id (ofs' ++ ofs) (cat st' st), Cs.union ctrs' ctrs))
                             where
                              ret = case (nms',nms) of
                                      (Nothing,Nothing) -> Nothing
                                      (Just l, Nothing) -> error "TODO"
                                      (Nothing,Just l)  -> error "TODO"
                                      (Just l1,Just l2) -> Just $ l1 ++ l2
  where
    cat :: Type -> Type -> Type
    cat TUnit      tp            = tp
    cat tp         TUnit         = tp
    cat (TTuple l1) (TTuple l2)  = TTuple $ l1 ++ l2
    cat (TTuple l1) tp           = TTuple $ l1 ++ [tp]
    cat tp         (TTuple l2)   = TTuple $ tp :  l2
    cat tp1        tp2           = TTuple $ [tp1,tp2]

-------------------------------------------------------------------------------

fvar :: [Stmt] -> TypeC -> TypeC
fvar ds (tp_,ctrs) = (fvar' ds tp_, ctrs)
  where
    fvar' :: [Stmt] -> Type -> Type
    fvar' ds (TData hier ofs st) = TData hier ofs $
      case find (\(SData'' _ _ (TData h' _ _,_) _ _) -> h'==hier) ds of
        Nothing -> fvar' ds st
        Just (SData'' _ _ (TData _ ofs' st',_) _ _)
                -> instantiate (zip (map (\(TAny v)->v) ofs') ofs) st'
    fvar' ds (TFunc inp out)  = TFunc (fvar' ds inp) (fvar' ds out)
    fvar' ds (TTuple tps)     = TTuple $ map (fvar' ds) tps
    fvar' _  tp               = tp

-------------------------------------------------------------------------------

-- accessors
-- data X with (...,Int,...)
-- X_2 : (X -> Int)

faccs :: Ann -> Maybe [ID_Var] -> TypeC -> Stmt -> Stmt
faccs z nms (tpD@(TData hr _ st),cz) p = accs where
  (accs,_) = foldr f (p, 1) (g st)

  hr_str = hier2str hr

  g :: Type -> [Type]
  g (TTuple l) = l
  g TUnit      = []
  g tp         = [tp]

  f :: Type -> (Stmt,Int) -> (Stmt,Int)
  f tp (p,idx) = (SVar'' z id (TFunc tpD tp,cz)
                    (SMatch' z False body [(SNop z, EVar z id, nm p)])
                 ,idx+1)
                 where
                  id = hr_str ++ "._" ++ show idx

                  body = EFunc z Nothing (TFunc tpD tp,cz)
                          (SVar'' z "ret" (tp,cz)
                            (SMatch' z False (EArg z) [(SNop z, ret, SRet z (EVar z "ret"))]))
                  ret  = ECall z (ECons z hr) (bool (ETuple z repl) (repl!!0) (len st == 1))
                  repl = take (idx-1) anys ++ [EVar z "ret"] ++ drop idx anys
                  anys = replicate (len st) (EAny z)

                  len (TTuple l) = length l
                  len _          = 1

                  nm p = case nms of
                          Nothing -> p
                          Just l  -> SVar'' z idm (TFunc tpD tp,cz)
                                      (SMatch' z False body [(SNop z, EVar z idm, p)])
                                     where
                                      idm = hr_str ++ "." ++ (l!!(idx-1))
                                      body = EFunc z Nothing (TFunc tpD tp,cz)
                                              (SRet z (ECall z (EVar z id) (EArg z)))
