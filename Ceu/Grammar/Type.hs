module Ceu.Grammar.Type where

import Debug.Trace
import Data.Maybe (fromJust)
import Data.List (sortBy, groupBy, find, intercalate, isPrefixOf)
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

show' :: Type -> String
show' (TypeV id)      = id
show' TypeT           = "top"
show' TypeB           = "bot"
show' Type0           = "()"
show' (Type1 id)      = id
show' (TypeF inp out) = "(" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TypeN tps)     = "(" ++ intercalate "," (map show' tps) ++ ")"

-------------------------------------------------------------------------------

isSupOf :: Type -> Type -> Bool

isSupOf (TypeV _)         _                 = True
isSupOf _                 (TypeV _)         = False

isSupOf TypeT             _                 = True
isSupOf _                 TypeT             = True

isSupOf TypeB             _                 = False
isSupOf _                 TypeB             = False

isSupOf Type0             Type0             = True
isSupOf Type0             _                 = False
isSupOf _                 Type0             = False

isSupOf (Type1 t1)        (Type1 t2)        = (t1 `isPrefixOf` t2)
isSupOf (Type1 _)         _                 = False
isSupOf _                 (Type1 _)         = False

isSupOf (TypeF inp1 out1) (TypeF inp2 out2) = (inp1 `isSupOf` inp2) && (out1 `isSupOf` out2)
isSupOf (TypeF _    _)    _                 = False
isSupOf _                 (TypeF _    _)    = False

isSupOf (TypeN t1s)       (TypeN t2s)       = (t1s `isSupOfN` t2s) && (t1s `isSupOfV` t2s)

    where
        isSupOfN :: [Type] -> [Type] -> Bool
        isSupOfN []      []      = True
        isSupOfN []      _       = False
        isSupOfN _       []      = False
        isSupOfN (t1:l1) (t2:l2) = (t1 `isSupOf` t2) && (TypeN l1 `isSupOf` TypeN l2)

        isSupOfV :: [Type] -> [Type] -> Bool
        isSupOfV vars tps = ok                     -- [k,"a","b","a"] ["Int","Int","Bool","Int"]
            where
                grouped = groupTypesV vars tps        -- [[("a",I),("a",I)], [("b",B)]]
                mapped  = map (map snd) grouped       -- [["Int","Int"], ["Bool"]]
                equals  = map (\l -> all (== head l) l) mapped
                                                      -- [True, True]
                ok      = all id equals               -- True

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

instantiate :: Type -> (Type,Type) -> Type -- TypeV -> (TypeV|~TypeV,~TypeV) -> ~TypeV
instantiate tp (tp1, tp2) = aux tp (flatten tp1, flatten tp2)
    where
        flatten (TypeF inp out) = flatten inp ++ flatten out
        flatten (TypeN tps)     = concatMap flatten tps
        flatten tp              = [tp]

        aux :: Type -> ([Type],[Type]) -> Type -- TypeV -> ([TypeV|~TypeV],[~TypeV]) -> ~TypeV
        aux (TypeV var) (vars,tps) = tp
            where
                grouped = groupTypesV vars tps -- [[("a",I),("a",I)], [("b",B)]]
                singles = map head grouped     -- [("a",I), ("b",B)]
                tp'     = find (\(TypeV var',_) -> var==var') singles -- ("b",B)
                tp      = snd $ fromJust tp'
        aux tp _ = tp

-------------------------------------------------------------------------------

isParametric :: Type -> Bool
isParametric (TypeV _)     = True
isParametric (TypeF t1 t2) = isParametric t1 || isParametric t2
isParametric (TypeN l)     = foldr (\tp acc -> isParametric tp || acc) False l
isParametric _             = False

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
