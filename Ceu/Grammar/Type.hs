module Ceu.Grammar.Type where

import Debug.Trace
import Data.Maybe (fromJust)
import Data.List (sortBy, groupBy, find)
import Ceu.Grammar.Globals

data Type = TypeB
          | TypeT
          | Type0
          | Type1 ID_Type
          | TypeN [Type]    -- (len >= 2)
          | TypeF Type Type
          | TypeV ID_Var
    deriving (Eq,Show)

-------------------------------------------------------------------------------

checkTypes :: Type -> Type -> Bool

checkTypes (TypeV _)         _                 = True
checkTypes _                 (TypeV _)         = False

checkTypes TypeT             _                 = True
checkTypes _                 TypeT             = True

checkTypes TypeB             _                 = False
checkTypes _                 TypeB             = False

checkTypes Type0             Type0             = True
checkTypes Type0             _                 = False
checkTypes _                 Type0             = False

checkTypes (Type1 t1)        (Type1 t2)        = (t1 == t2)
checkTypes (Type1 _)         _                 = False
checkTypes _                 (Type1 _)         = False

checkTypes (TypeF inp1 out1) (TypeF inp2 out2) = (checkTypes inp1 inp2) && (checkTypes out1 out2)
checkTypes (TypeF _    _)    _                 = False
checkTypes _                 (TypeF _    _)    = False

checkTypes (TypeN t1s)       (TypeN t2s)       = (checkTypesN t1s t2s) && (checkTypesV t1s t2s)

-------------------------------------------------------------------------------

get1s :: Type -> [ID_Type]

get1s (TypeV _)       = []
get1s TypeT           = []
get1s TypeB           = []
get1s Type0           = []
get1s (Type1 v)       = [v]
get1s (TypeF inp out) = get1s inp ++ get1s out
get1s (TypeN ts)      = concatMap get1s ts

-------------------------------------------------------------------------------

checkTypesN :: [Type] -> [Type] -> Bool
checkTypesN []      []      = True
checkTypesN []      _       = False
checkTypesN _       []      = False
checkTypesN (t1:l1) (t2:l2) = (checkTypes t1 t2) && (checkTypes (TypeN l1) (TypeN l2))

-------------------------------------------------------------------------------

checkTypesV :: [Type] -> [Type] -> Bool
checkTypesV vars tps = ok                     -- [k,"a","b","a"] ["Int","Int","Bool","Int"]
    where
        grouped = groupTypesV vars tps        -- [[("a",I),("a",I)], [("b",B)]]
        mapped  = map (map snd) grouped       -- [["Int","Int"], ["Bool"]]
        equals  = map (\l -> all (== head l) l) mapped
                                              -- [True, True]
        ok      = all id equals               -- True

-------------------------------------------------------------------------------

groupTypesV :: [Type] -> [Type] -> [[(Type,Type)]] -- [TypeV|~TypeV] -> [~TypeV] -> [[(TypeV,~TypeV)]]
groupTypesV vars tps = grouped                -- [k,"a","b","a"] ["Int","Int","Bool","Int"]
    where
        zipped  = zip vars tps                -- [(k,I),("a",I),("b",B),("a",I)]
        filterd = filter (isTypeV.fst) zipped -- [("a",I), ("b",B), ("a",I)]
        sorted  = sortBy (\((TypeV t1),_) ((TypeV t2),_) -> compare t1 t2) filterd
                                              -- [("a",I), ("a",I), ("b",B)]
        grouped = groupBy (\(x,_)(y,_)->x==y) sorted -- [[("a",I),("a",I)], [("b",B)]]

        isTypeV (TypeV _) = True
        isTypeV _         = False


-------------------------------------------------------------------------------

instType :: Type -> (Type,Type) -> Type -- TypeV -> (TypeV|~TypeV,~TypeV) -> ~TypeV
instType tp (TypeN tps1, TypeN tps2) = instType' tp (tps1,tps2)
instType tp (tp1,        tp2)        = instType' tp ([tp1],[tp2])

instType' :: Type -> ([Type],[Type]) -> Type -- TypeV -> ([TypeV|~TypeV],[~TypeV]) -> ~TypeV
instType' (TypeV var) (vars,tps) = tp
    where
        grouped = groupTypesV vars tps          -- [[("a",I),("a",I)], [("b",B)]]
        singles = map head grouped              -- [("a",I), ("b",B)]
        tp'     = find (\(TypeV var',_) -> var==var') singles -- ("b",B)
        tp      = snd $ fromJust tp'
instType' tp _ = tp

-------------------------------------------------------------------------------

isPolymorphic :: Type -> Bool
isPolymorphic (TypeV _)     = True
isPolymorphic (TypeF t1 t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TypeN l)     = foldr (\tp acc -> isPolymorphic tp || acc) False l
isPolymorphic _             = False

-------------------------------------------------------------------------------

{-
reducesToType0 :: Type -> Bool
reducesToType0 Type0     = True
reducesToType0 (TypeN l) = foldr (\tp acc -> reducesToType0 tp && acc) True l
reducesToType0 _         = False

toTypeN :: Type -> Type
toTypeN (TypeN tps) = TypeN tps
toTypeN Type0       = TypeN []
toTypeN (Type1 tp)  = TypeN [Type1 tp]
toTypeN tp          = error $ show tp
-}
