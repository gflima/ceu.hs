module Ceu.Grammar.Type where

import Debug.Trace
import Data.Maybe  (fromJust)
import Data.Either (isRight)
import Data.List   (sortBy, groupBy, find, intercalate, isPrefixOf)
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

get1s :: Type -> [ID_Type]

get1s (TypeV _)       = []
get1s TypeT           = []
get1s TypeB           = []
get1s Type0           = []
get1s (Type1 v)       = [v]
get1s (TypeF inp out) = get1s inp ++ get1s out
get1s (TypeN ts)      = concatMap get1s ts

-------------------------------------------------------------------------------

-- list: list with instantiated pairs (var,Type)
-- Type: type (possibly TypeV) we want to instantiate
-- Type: type of the instantiated variable
instantiate :: [(ID_Var,Type)] -> Type -> Type
instantiate vars (TypeV var)     = snd $ fromJust $ find (\(var',_) -> var==var') vars
instantiate vars (TypeF inp out) = TypeF (instantiate vars inp) (instantiate vars out)
instantiate vars (TypeN tps)     = TypeN $ map (instantiate vars) tps
instantiate _    tp              = tp

-------------------------------------------------------------------------------

isSupOf :: Type -> Type -> Bool
isSupOf sup sub = isRight $ sup `supOf` sub

isSubOf :: Type -> Type -> Bool
isSubOf sub sup = isRight $ sup `supOf` sub

supOfErrors :: Type -> Type -> Errors
supOfErrors sup sub = either id (const []) (sup `supOf` sub)

supOf :: Type -> Type -> Either Errors (Type, [(ID_Var,Type)])
supOf sup sub =
  if ret && null es_inst
    then Right (tp, singles)
    else Left $ es_tps ++ es_inst
  where
    (ret, tp, insts) = sup `supOf'` sub

    es_tps = ["types do not match : expected '" ++ show' sup ++
              "' : found '" ++ show' sub ++ "'"]

    sorted  = sortBy (\(a,_)(b,_) -> compare a b) insts -- [("a",A),("a",A),("b",B)]
    grouped = groupBy (\(x,_)(y,_)->x==y) sorted        -- [[("a",A),("a",A)], [("b",B)]]
    es_inst = concatMap f grouped
    f l@((var,tp):m) = if all (== (var,tp)) m then [] else
                        ["ambigous instances for '" ++ var ++ "' : " ++
                         intercalate ", " (map (quote.show'.snd) l)]
    singles = map head grouped                    -- [("a",A), ("b",B)]
    quote x = "'" ++ x ++ "'"

-------------------------------------------------------------------------------

-- Is first argument a supertype of second argument?
--  * Bool: whether it is or not
--  * Type: most specific type between the two (second argument on success, first otherwise)
--  * list: all instantiations of parametric types [(a,X),(b,Y),(a,X),...]

supOf' :: Type -> Type -> (Bool, Type, [(ID_Var,Type)])

supOf' _                 TypeB             = (True,  TypeB, [])
supOf' TypeB             _                 = (False, TypeB, [])

supOf' TypeT             sub               = (True,  sub,   [])
supOf' (TypeV a1)        sub               = (True,  sub,   [(a1,sub)])
supOf' _                 sub@(TypeV _)     = (True,  sub,   [])
supOf' sup               TypeT             = (False, sup,   [])

supOf' Type0             Type0             = (True,  Type0, [])
supOf' Type0             _                 = (False, Type0, [])
supOf' sup               Type0             = (False, sup,   [])

supOf' sup@(Type1 x)     sub@(Type1 y)
  | x `isPrefixOf` y                       = (True,  sub,   [])
  | otherwise                              = (False, sup,   [])

supOf' sup@(Type1 _)     _                 = (False, sup,   [])
supOf' sup               (Type1 _)         = (False, sup,   [])

supOf' sup@(TypeF inp1 out1) sub@(TypeF inp2 out2) =
  let (i,_,k) = inp1 `supOf'` inp2
      (x,_,z) = out1 `supOf'` out2 in
    if i && x then                           (True,  sub,   k++z)
              else                           (False, sup,   k++z)

supOf' sup@(TypeF _ _)   _                 = (False, sup,   [])
supOf' sup               (TypeF _ _)       = (False, sup,   [])

supOf' (TypeN sups)      (TypeN subs)      = foldr f (True, TypeN [], []) $
                                              zipWith supOf' sups subs
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
