module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type               (Type(..),TypeC,instantiate,getSuper)
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
stmt ds (Data''  z id  vs tp abs p)   = Data''' z id  tp' abs (stmt (d':ds) p)
                                        where
                                          tp' = fdata ds (id,vs) tp
                                          d'  = Data'' z id vs tp' abs p
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

fdata :: [Stmt] -> (ID_Data_Hier,[ID_Var]) -> TypeC -> TypeC
fdata ds (id,vars) tp = case getSuper id of
  Nothing  -> tp
  Just sup -> case find (\(Data'' _ id' _ _ _ _) -> id'==sup) ds of
                Nothing                         -> tp
                Just (Data'' _ _ vars' tp' _ _) ->
                  case any (\v2 -> elem v2 vars) vars' of
                    True  -> error $ "TODO: repeated variables"
                    False -> cat tp tp'
  where
    cat :: TypeC -> TypeC -> TypeC
    cat (tp1_,ctrs1) (tp2_,ctrs2) = (cat' tp1_ tp2_, Cs.union ctrs1 ctrs2)

    cat' :: Type -> Type -> Type
    cat' Type0      tp              = tp
    cat' tp         Type0           = tp
    cat' (TypeN l1) (TypeN l2)      = TypeN $ l1 ++ l2
    cat' (TypeN l1) tp              = TypeN $ l1 ++ [tp]
    cat' tp         (TypeN l2)      = TypeN $ tp :  l2
    cat' tp1        tp2             = TypeN $ [tp1,tp2]

-------------------------------------------------------------------------------

fvar :: [Stmt] -> TypeC -> TypeC
fvar ds (tp_,ctrs) = (fvar' ds tp_, ctrs)
  where
    fvar' :: [Stmt] -> Type -> Type
    fvar' ds (TypeD hier tp_) = TypeD hier $
      case find (\(Data'' _ h' _ _ _ _) -> h'==hier) ds of
        Nothing                             -> fvar' ds tp_
        Just (Data'' _ _ vars (tp_',_) _ _) -> instantiate (zip vars tps_) tp_' where
                                                tps_ = case fvar' ds tp_ of
                                                  TypeN x -> x
                                                  Type0   -> []
                                                  x       -> [x]
    fvar' ds (TypeF inp out)  = TypeF (fvar' ds inp) (fvar' ds out)
    fvar' ds (TypeN tps)      = TypeN $ map (fvar' ds) tps
    fvar' _  tp               = tp
