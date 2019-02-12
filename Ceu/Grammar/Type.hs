module Ceu.Grammar.Type where

import Debug.Trace
import Data.Bool   (bool)
import Data.Maybe  (fromJust)
import Data.Either (isRight)
import Data.List   (sortBy, groupBy, find, intercalate, isPrefixOf)
import Ceu.Grammar.Globals

data Type = TypeB
          | TypeT
          | Type0
          | Type1 [ID_Type]
          | TypeN [Type]    -- (len >= 2)
          | TypeF Type Type
          | TypeV ID_Var
    deriving (Eq,Show)

-------------------------------------------------------------------------------

hier2str = intercalate "."

show' :: Type -> String
show' (TypeV id)      = id
show' TypeT           = "top"
show' TypeB           = "bot"
show' Type0           = "()"
show' (Type1 hier)    = hier2str hier
show' (TypeF inp out) = "(" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TypeN tps)     = "(" ++ intercalate "," (map show' tps) ++ ")"

-------------------------------------------------------------------------------

get1s :: Type -> [ID_Type]

get1s (TypeV _)       = []
get1s TypeT           = []
get1s TypeB           = []
get1s Type0           = []
get1s (Type1 hier)    = [hier2str hier]
get1s (TypeF inp out) = get1s inp ++ get1s out
get1s (TypeN ts)      = concatMap get1s ts

-------------------------------------------------------------------------------

getSuper :: Type -> Maybe Type
getSuper (Type1 [_])  = Nothing
getSuper (Type1 hier) = Just $ Type1 (init hier)
getSuper _            = error "bug found : expecting `Type1`"

splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d [] = []
splitOn d s = x : splitOn d (drop 1 y) where (x,y) = span (/= d) s

-------------------------------------------------------------------------------

cat :: Type -> Type -> Type
cat Type0      tp              = tp
cat tp         Type0           = tp
cat (TypeN l1) (TypeN l2)      = TypeN $ l1 ++ l2
cat (TypeN l1) tp              = TypeN $ l1 ++ [tp]
cat tp         (TypeN l2)      = TypeN $ tp :  l2
cat tp1        tp2             = TypeN $ [tp1,tp2]

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
isSupOf sup sub = b where (b,_,_) = sup `supOf'` sub

isSubOf :: Type -> Type -> Bool
isSubOf sub sup = b where (b,_,_) = sup `supOf'` sub

supOfErrors :: Type -> Type -> Errors
supOfErrors sup sub = either id (const []) (sup `supOf` sub)

supOf :: Type -> Type -> Either Errors (Type, [(ID_Var,Type)])
supOf sup sub =
  if ret && null es_inst then Right (tp, singles)
                         else Left $ es_tps ++ es_inst
  where
    (ret, tp, insts) = sup `supOf'` sub

    es_tps = ["types do not match : expected '" ++ show' sup ++
              "' : found '" ++ show' sub ++ "'"]

    sorted  = sortBy (\(a,_,_)(b,_,_) -> compare a b) insts -- [("a",A,>),("a",A,<),("b",B,>)]
    grouped = groupBy (\(x,_,_)(y,_,_)->x==y) sorted        -- [[("a",A,>),("a",A,<)], [("b",B,>)]]
    es_inst = concatMap f grouped

    f l@((var,_,_):_) =
      let sups    = map gettp $ filter isSup       l
          subs    = map gettp $ filter (not.isSup) l
          min_tp  = min sups
          max_tp  = max subs
          sups_ok = sups==[] || all (isSupOf min_tp) sups
          subs_ok = subs==[] || all (isSubOf max_tp) subs
          ok      = sups_ok && subs_ok &&
                    (sups==[] || subs==[] || max_tp `isSupOf` min_tp)
      in
        if ok then [] else
          if sups_ok && subs_ok && sups/=[] && subs/=[] && (max_tp `isSubOf` min_tp) then
            ["type variance does not match : '" ++ show' max_tp ++
                   "' should be supertype of '" ++ show' min_tp ++ "'"]
          else
            ["ambigous instances for '" ++ var ++ "' : " ++
             intercalate ", " (map (quote.show'.gettp) l)]

    gettp (_,tp,_) = tp
    isSup (_, _,v) = v

    singles = map ((\(var,tp,_)->(var,tp)).head) grouped    -- [("a",A), ("b",B)]
    quote x = "'" ++ x ++ "'"

    -- the types have no total order but there should be a min
    --sort' :: Bool -> [Type] -> Type
    max tps = head $ sortBy (\t1 t2 -> bool LT GT (t1 `isSupOf` t2)) tps
    min tps = head $ sortBy (\t1 t2 -> bool LT GT (t1 `isSubOf` t2)) tps

-------------------------------------------------------------------------------

-- Is first argument a supertype of second argument?
--  * Bool: whether it is or not
--  * Type: most specific type between the two (second argument on success, first otherwise)
--  * list: all instantiations of parametric types [(a,X),(b,Y),(a,X),...]

supOf' :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Bool)])
                                        -- "a" >= tp (True)
                                        -- "a" <= tp (False)

supOf' TypeT             TypeT             = (True,  TypeT, [])
supOf' sup               TypeT             = (False, sup,   [])
supOf' TypeT             sub               = (True,  sub,   [])

supOf' _                 TypeB             = (True,  TypeB, [])
supOf' TypeB             _                 = (False, TypeB, [])

supOf' sup@(TypeV a1)    sub@(TypeV a2)    = (True,  sub,   [(a1,sub,True),(a2,sup,False)])
supOf' (TypeV a1)        sub               = (True,  sub,   [(a1,sub,True)])
supOf' sup               sub@(TypeV a2)    = (True,  sub,   [(a2,sup,False)])

supOf' Type0             Type0             = (True,  Type0, [])
supOf' Type0             _                 = (False, Type0, [])
supOf' sup               Type0             = (False, sup,   [])

supOf' sup@(Type1 x)     sub@(Type1 y)
  | x `isPrefixOf` y                       = (True,  sub,   [])
  | otherwise                              = (False, sup,   [])

supOf' sup@(Type1 _)     _                 = (False, sup,   [])
supOf' sup               (Type1 _)         = (False, sup,   [])

supOf' sup@(TypeF inp1 out1) sub@(TypeF inp2 out2) =
  let (i,_,k) = inp2 `supOf'` inp1      -- contravariance on inputs
      (x,_,z) = out1 `supOf'` out2 in
    if i && x then                           (True,  sub,   k++z)
              else                           (False, sup,   k++z)

supOf' sup@(TypeF _ _)   _                 = (False, sup,   [])
supOf' sup               (TypeF _ _)       = (False, sup,   [])

supOf' (TypeN sups)      (TypeN subs)      = foldr f (True, TypeN [], []) $
                                              zipWith supOf' (sups++bots) (subs++tops)
  where
    bots = replicate (length subs - length sups) TypeB
    tops = replicate (length sups - length subs) TypeT
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
