module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..),TypeC,instantiate)
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

stmt :: [Stmt] -> Stmt -> Stmt
stmt ds   (Class'' z id  cs ifc p)      = Class'' z id  cs ifc (stmt ds p)
stmt ds   (Inst''  z cls tp imp p)      = Inst''  z cls tp imp (stmt ds p)
stmt ds d@(Data''  z id  vs tp abs p)   = Data''' z id  tp abs (stmt (d:ds) p)
stmt ds   (Var''   z var tp p)          = Var''   z var (f ds tp) (stmt ds p)
stmt ds   (Match'  z chk loc exp p1 p2) = Match'  z chk loc (expr ds exp) (stmt ds p1) (stmt ds p2)
stmt ds   (CallS   z exp)               = CallS   z (expr ds exp)
stmt ds   (Seq     z p1 p2)             = Seq     z (stmt ds p1) (stmt ds p2)
stmt ds   (Loop    z p)                 = Loop    z (stmt ds p)
stmt ds   (Ret     z exp)               = Ret     z (expr ds exp)
stmt _    p                             = p

expr :: [Stmt] -> Exp -> Exp
expr ds (Call z e1 e2)                  = Call    z (expr ds e1) (expr ds e2)
expr ds (Func z tp p)                   = Func    z tp (stmt ds p)
expr _  e                               = e

f :: [Stmt] -> TypeC -> TypeC
f ds (tp_,ctrs) = (f' ds tp_, ctrs)

f' :: [Stmt] -> Type -> Type
f' ds (TypeD hier tp_) = TypeD hier $
  case find (\(Data'' _ h' _ _ _ _) -> h'==hier) ds of
    Nothing                             -> f' ds tp_
    Just (Data'' _ _ vars (tp_',_) _ _) -> instantiate (zip vars tps_) tp_' where
                                          TypeN tps_ = f' ds tp_
f' ds (TypeF inp out)  = TypeF (f' ds inp) (f' ds out)
f' ds (TypeN tps)      = TypeN $ map (f' ds) tps
f' _  tp               = tp
