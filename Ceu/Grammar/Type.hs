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

{-
-- ID_Var: variable we want to instantiate
-- Type:   supertype with the variable
-- Type:   subtype with the concretes
-- Type:   type of the instantiated variable
instantiate' :: ID_Var -> Type -> Type -> Type
instantiate' var tp1 tp2 =
  let (ret, tp, insts) = tp1 `supOf'` tp2 in
    





 (tp1, tp2) = aux tp (flatten tp1, flatten tp2)
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
-}

-------------------------------------------------------------------------------

supOf :: Type -> Type -> Either Errors (Type, [(ID_Var,Type)])
supOf tp1 tp2 =
  if ret && null es_inst
    then Right (tp, singles)
    else Left $ es_tps ++ es_inst
  where
    (ret, tp, insts) = tp1 `supOf'` tp2

    es_tps = ["types do not match : expected '" ++ show' tp1 ++
              "' : found '" ++ show' tp2 ++ "'"]

    sorted  = sortBy (\(a,_)(b,_) -> compare a b) insts -- [("a",A),("a",A),("b",B)]
    grouped = groupBy (\(x,_)(y,_)->x==y) sorted        -- [[("a",A),("a",A)], [("b",B)]]
    es_inst = concatMap f grouped
    f l@((var,tp):m) = if all (== (var,tp)) m then [] else
                        ["ambigous instances for '" ++ var ++ "' : " ++
                         intercalate ", " (map (quote.show'.snd) l)]
    singles = map head grouped                    -- [("a",A), ("b",B)]
    quote x = "'" ++ x ++ "'"

-- Is first argument a supertype of second argument?
--  * Bool: whether it is or not
--  * Type: most specific type between the two (second argument on success, first otherwise)
--  * list: all instantiations of parametric types [(a,X),(b,Y),(a,X),...]

supOf' :: Type -> Type -> (Bool, Type, [(ID_Var,Type)])

supOf' _                 TypeB             = (True,  TypeB, [])
supOf' TypeB             _                 = (False, TypeB, [])

supOf' TypeT             tp2               = (True,  tp2,   [])
supOf' (TypeV a1)        tp2               = (True,  tp2,   [(a1,tp2)])
supOf' tp1               (TypeV _)         = (False, tp1,   [])
supOf' tp1               TypeT             = (False, tp1,   [])

supOf' Type0             Type0             = (True,  Type0, [])
supOf' Type0             _                 = (False, Type0, [])
supOf' tp1               Type0             = (False, tp1,   [])

supOf' tp1@(Type1 x)     tp2@(Type1 y)
  | x `isPrefixOf` y                       = (True,  tp2,   [])
  | otherwise                              = (False, tp1,   [])

supOf' tp1@(Type1 _)     _                 = (False, tp1,   [])
supOf' tp1               (Type1 _)         = (False, tp1,   [])

supOf' tp1@(TypeF inp1 out1) tp2@(TypeF inp2 out2) =
  let (i,_,k) = inp1 `supOf'` inp2
      (x,_,z) = out1 `supOf'` out2 in
    if i && x then                           (True,  tp2,   k++z)
              else                           (False, tp1,   k++z)

supOf' tp1@(TypeF _ _)   _                 = (False, tp1,   [])
supOf' tp1               (TypeF _ _)       = (False, tp1,   [])

supOf' (TypeN tp1s)      (TypeN tp2s)      = foldr f (True, TypeN [], []) $
                                              zipWith supOf' tp1s tp2s
  where
    f (ret, tp, insts) (ret', TypeN tps', insts') =
      (ret&&ret', TypeN (tp:tps'), insts++insts')

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
