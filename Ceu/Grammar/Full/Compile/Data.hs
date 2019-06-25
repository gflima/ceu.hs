module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type               (Type(..),TypeC,instantiate,getSuper,getVs)
import Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt [] p

-- Instantiates variable declarations of TypeD with their complete types:
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
stmt ds (Class'' z id  cs ifc p)      = Class'' z id  cs ifc (stmt ds p)
stmt ds (Inst''  z cls tp imp p)      = Inst''  z cls tp imp (stmt ds p)
stmt ds (Data''  z tp abs p)          = Data''  z tp' abs (stmt (d':ds) p)
                                        where
                                          tp' = fdata ds tp
                                          d'  = Data'' z tp' abs p
stmt ds (Var''   z var tp p)          = Var''   z var (fvar ds tp) (stmt ds p)
stmt ds (Match'  z chk loc exp p1 p2) = Match'  z chk loc (expr ds exp) (stmt ds p1) (stmt ds p2)
stmt ds (CallS   z exp)               = CallS   z (expr ds exp)
stmt ds (Seq     z p1 p2)             = Seq     z (stmt ds p1) (stmt ds p2)
stmt ds (Loop    z p)                 = Loop    z (stmt ds p)
stmt ds (Ret     z exp)               = Ret     z (expr ds exp)
stmt _  p                             = p

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> Exp
expr ds (Call z e1 e2)                  = Call    z (expr ds e1) (expr ds e2)
expr ds (Func z tp p)                   = Func    z tp (stmt ds p)
expr _  e                               = e

-------------------------------------------------------------------------------

fdata :: [Stmt] -> TypeC -> TypeC
fdata ds tp@(TypeD id tpof tpst, ctrs) = case getSuper id of
  Nothing  -> tp
  Just sup -> case find (\(Data'' _ (TypeD id' _ _,_) _ _) -> id'==sup) ds of
                Nothing -> tp
                Just (Data'' _ (TypeD _ tpof' tpst',ctrs') _ _) ->
                  case any (\v2 -> elem v2 (getVs tpof)) (getVs tpof') of
                    True  -> error $ "TODO: repeated variables"
                    False -> (TypeD id (cat tpof tpof') (cat tpst tpst'), Cs.union ctrs ctrs')
  where
    cat :: Type -> Type -> Type
    cat Type0      tp              = tp
    cat tp         Type0           = tp
    cat (TypeN l1) (TypeN l2)      = TypeN $ l1 ++ l2
    cat (TypeN l1) tp              = TypeN $ l1 ++ [tp]
    cat tp         (TypeN l2)      = TypeN $ tp :  l2
    cat tp1        tp2             = TypeN $ [tp1,tp2]

-------------------------------------------------------------------------------

fvar :: [Stmt] -> TypeC -> TypeC
fvar ds (tp_,ctrs) = (fvar' ds tp_, ctrs)
  where
    fvar' :: [Stmt] -> Type -> Type
    fvar' ds (TypeD hier x tpst) = TypeD hier x $
      case find (\(Data'' _ (TypeD h' _ _,_) _ _) -> h'==hier) ds of
        Nothing -> fvar' ds tpst
        Just (Data'' _ (TypeD _ tpof' tpst',_) _ _)
                -> instantiate (zip (getVs tpof') tps_) tpst'
                   where
                     tps_ = case fvar' ds tpst of
                       TypeN x -> x
                       Type0   -> []
                       x       -> [x]
    fvar' ds (TypeF inp out)  = TypeF (fvar' ds inp) (fvar' ds out)
    fvar' ds (TypeN tps)      = TypeN $ map (fvar' ds) tps
    fvar' _  tp               = tp
