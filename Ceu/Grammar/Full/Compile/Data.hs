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
stmt ds (Class'' z id  cs ifc p) = Class'' z id  cs ifc (stmt ds p)
stmt ds (Inst''  z cls tp imp p) = Inst''  z cls tp imp (stmt ds p)
stmt ds (Data''  z tp abs p)     = Data''  z tp' abs (stmt (d':ds) (faccs z tp' p))
                                   where
                                     tp' = fdata ds tp
                                     d'  = Data'' z tp' abs p
stmt ds (Var''   z var tp p)     = Var''   z var (fvar ds tp) (stmt ds p)
stmt ds (Match'  z chk exp cses) = Match'  z chk (expr ds exp)
                                     (map (\(xs,pt,st) -> (stmt ds xs, expr ds pt, stmt ds st)) cses)
stmt ds (CallS   z exp)          = CallS   z (expr ds exp)
stmt ds (Seq     z p1 p2)        = Seq     z (stmt ds p1) (stmt ds p2)
stmt ds (Loop    z p)            = Loop    z (stmt ds p)
stmt ds (Ret     z exp)          = Ret     z (expr ds exp)
stmt _  p                        = p

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> Exp
expr ds (ETuple z es)            = ETuple z (map (expr ds) es)
expr ds (ECall  z e1 e2)         = ECall  z (expr ds e1) (expr ds e2)
expr ds (EFunc  z tp p)          = EFunc  z tp (stmt ds p)
expr _  e                        = e

-------------------------------------------------------------------------------

fdata :: [Stmt] -> TypeC -> TypeC
fdata ds tp@(TData id ofs st, ctrs) = case getSuper id of
  Nothing  -> tp
  Just sup -> case find (\(Data'' _ (TData id' _ _,_) _ _) -> id'==sup) ds of
                Nothing -> tp
                Just (Data'' _ (TData _ ofs' st',ctrs') _ _) ->
                  case any (\v2 -> elem v2 ofs) ofs' of
                    True  -> error $ "TODO: repeated variables"
                    False -> (TData id (ofs ++ ofs') (cat st st'), Cs.union ctrs ctrs')
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
      case find (\(Data'' _ (TData h' _ _,_) _ _) -> h'==hier) ds of
        Nothing -> fvar' ds st
        Just (Data'' _ (TData _ ofs' st',_) _ _)
                -> instantiate (zip (map (\(TAny v)->v) ofs') ofs) st'
    fvar' ds (TFunc inp out)  = TFunc (fvar' ds inp) (fvar' ds out)
    fvar' ds (TTuple tps)     = TTuple $ map (fvar' ds) tps
    fvar' _  tp               = tp

-------------------------------------------------------------------------------

-- accessors
-- data X with (...,Int,...)
-- X_2 : (X -> Int)

faccs :: Ann -> TypeC -> Stmt -> Stmt
faccs z (tpD@(TData hr _ st),cz) p = accs where
  (accs,_) = foldr f (p, 1) (g st)

  hr_str = hier2str hr

  g :: Type -> [Type]
  g (TTuple l) = l
  g TUnit      = []
  g tp         = [tp]

  f :: Type -> (Stmt,Int) -> (Stmt,Int)
  f tp (p,idx) = (Var'' z id (TFunc tpD tp,cz)
                    (Match' z False body [(Nop z, EVar z id, p)])
                 ,idx+1)
                 where
                  id = hr_str ++ "._" ++ show idx

                  body = EFunc z (TFunc tpD tp,cz)
                          (Var'' z "ret" (tp,cz)
                            (Match' z False (EArg z) [(Nop z, ret, Ret z (EVar z "ret"))]))
                  ret  = ECall z (ECons z hr) (bool (ETuple z repl) (repl!!0) (len st == 1))
                  repl = take (idx-1) anys ++ [EVar z "ret"] ++ drop idx anys
                  anys = replicate (len st) (EAny z)

                  len (TTuple l) = length l
                  len _          = 1
