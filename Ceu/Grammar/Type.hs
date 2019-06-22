module Ceu.Grammar.Type where

import Control.Exception (assert)
import Debug.Trace
import Data.Bool   (bool)
import Data.Maybe  (fromJust, isJust)
import Data.Either (isRight)
import Data.List   (sortBy, groupBy, find, intercalate, isPrefixOf)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Ceu.Grammar.Globals

data Type = TypeB
          | TypeT
          | Type0
          | TypeD ID_Data_Hier
          | TypeN [Type]    -- (len >= 2)
          | TypeF Type Type
          | TypeV ID_Var
    deriving (Eq,Show)

data Relation = SUP | SUB | ANY | NONE deriving (Eq, Show)

type Constraint  = (ID_Var,ID_Class)
type Constraints = Map.Map ID_Var (Set.Set ID_Class)

type TypeC = (Type, Constraints)

-------------------------------------------------------------------------------

hier2str = intercalate "."

show' :: Type -> String
show' (TypeV id)      = id
show' TypeT           = "top"
show' TypeB           = "bot"
show' Type0           = "()"
show' (TypeD hier)    = hier2str hier
show' (TypeF inp out) = "(" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TypeN tps)     = "(" ++ intercalate "," (map show' tps) ++ ")"

-------------------------------------------------------------------------------

getDs :: Type -> Set.Set ID_Data

getDs (TypeV _)       = Set.empty
getDs TypeT           = Set.empty
getDs TypeB           = Set.empty
getDs Type0           = Set.empty
getDs (TypeD hier)    = Set.singleton $ hier2str hier
getDs (TypeF inp out) = Set.union (getDs inp) (getDs out)
getDs (TypeN ts)      = Set.unions $ map getDs ts

-------------------------------------------------------------------------------

cz = Map.empty
cv :: ID_Var -> Constraints
cv var = Map.singleton var Set.empty
cvc :: Constraint -> Constraints
cvc (var,cls) = Map.singleton var $ Set.singleton cls

ctrsToList :: Constraints -> [(ID_Var,[ID_Class])]
ctrsToList ctrs = map (\(x,y) -> (x,Set.toList y)) $ Map.toList ctrs

ctrsInsert :: Constraint -> Constraints -> Constraints
ctrsInsert (var',cls') ctrs = Map.insertWith Set.union var' (Set.singleton cls') ctrs

ctrsHasClass :: ID_Class -> Constraints -> Bool
ctrsHasClass cls ctrs = any (Set.member cls) (Map.elems ctrs)

ctrsUnion :: Constraints -> Constraints -> Constraints
ctrsUnion ctrs1 ctrs2 = Map.unionWith Set.union ctrs1 ctrs2
{-
getConstraints :: Type -> Set.Set Constraint

getConstraints (TypeV _ [])     = Set.empty
getConstraints (TypeV var clss) = Set.singleton (var,clss)
getConstraints TypeT            = Set.empty
getConstraints TypeB            = Set.empty
getConstraints Type0            = Set.empty
getConstraints (TypeD hier)     = Set.empty
getConstraints (TypeF inp out)  = Set.union (getConstraints inp) (getConstraints out)
getConstraints (TypeN ts)       = Set.unions $ map getConstraints ts

hasAnyConstraint :: Type -> Bool
hasAnyConstraint tp = not $ Set.null $ getConstraints tp

hasConstraint :: ID_Class -> Type -> Bool
hasConstraint cls tp = not $ null $ Set.filter f $ getConstraints tp
                       where
                        f (var,clss) = elem cls clss

addConstraint (var,cls) Type0                      = Type0
addConstraint (var,cls) (TypeD x)                  = TypeD x
addConstraint (var,cls) (TypeN l)                  = TypeN $ map (addConstraint (var,cls)) l
addConstraint (var,cls) (TypeF inp out)            = TypeF (addConstraint (var,cls) inp) (addConstraint (var,cls) out)
addConstraint (var,cls) (TypeV var' l) | var==var' = TypeV var' (cls:l)
                                       | otherwise = TypeV var' l
-}

-------------------------------------------------------------------------------

getSuper :: Type -> Maybe Type
getSuper (TypeD [_])  = Nothing
getSuper (TypeD hier) = Just $ TypeD (init hier)
getSuper _            = error "bug found : expecting `TypeD`"

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
-- [(a,TypeD "Bool"),...] -> TypeV "a" -> TypeD "Bool"
instantiate :: [(ID_Var,Type)] -> Type -> Type
instantiate vars (TypeV var)    = case find (\(var',_) -> var==var') vars of
                                    Nothing    -> TypeV var
                                    Just (_,v) -> v
instantiate vars (TypeF inp out) = TypeF (instantiate vars inp) (instantiate vars out)
instantiate vars (TypeN tps)     = TypeN $ map (instantiate vars) tps
instantiate _    tp              = tp

-------------------------------------------------------------------------------

isRel :: Relation -> TypeC -> TypeC -> Bool
isRel rel (tp1_,_) (tp2_,_) = isRel_ rel tp1_ tp2_

isRel_ :: Relation -> Type -> Type -> Bool
isRel_ rel tp1 tp2 = either (const False) (const True) (relates_ rel tp1 tp2)

relatesErrors :: Relation -> TypeC -> TypeC -> Errors
relatesErrors rel (tp1_,_) (tp2_,_) = relatesErrors_ rel tp1_ tp2_

relatesErrors_ :: Relation -> Type -> Type -> Errors
relatesErrors_ rel tp1 tp2 = either id (const []) (relates_ rel tp1 tp2)

-- TODO: relates deve levar em consideracao os ctrs (e depende da REL)
relates :: Relation -> TypeC -> TypeC -> Either Errors (Type, [(ID_Var,Type)])
relates rel (tp1_,_) (tp2_,_) = relates_ rel tp1_ tp2_

relates_ :: Relation -> Type -> Type -> Either Errors (Type, [(ID_Var,Type)])
relates_ rel tp1 tp2 =
  if ret && null esi then Right (tp, right)
                     else Left $ es_tps ++ esi
  where
    (ret, tp, insts) = case rel of
                        SUP -> tp1 `supOf` tp2
                        SUB -> tp2 `supOf` tp1
                        ANY -> let (a,b,c) = tp1 `supOf` tp2
                                   (x,y,z) = tp2 `supOf` tp1 in
                                bool (a,b,c) (x,y,z) x

    es_tps = ["types do not match : expected '" ++ show' tp1 ++
              "' : found '" ++ show' tp2 ++ "'"]

    sorted  = sortBy (\(a,_,_)(b,_,_) -> compare a b) insts    -- [("a",A,SUP),("a",A,SUB),("b",B,SUP)]
    grouped = groupBy (\(x,_,_)(y,_,_)->x==y && x/="?") sorted -- [[("a",A,SUP),("a",A,SUB)], [("b",B,SUP)]]
    final   = map f grouped   -- [("a",Asub,[]), ("b",Bsub,[])]
    esi     = concatMap snd final
    right   = map       fst final

    f :: [(ID_Var,Type,Relation)] -> ((ID_Var,Type), Errors)
    f l@((var,_,_):_) = --traceShow l $
      let
          -- input
          sups    = comPre' $ map gettp $ filter isSUP l
          supest  = supest' sups
          sups_ok = all (isSupOf_ supest) sups

          -- output
          subs    = comPre' $ map gettp $ filter (not.isSUP) l
          subest  = subest' subs
          subs_ok = all (isSubOf subest) subs

          ok      = --traceShow (subs,supest, sups,subest)
                    sups_ok && subs_ok &&
                    (sups==[] || subs==[] || subest `isSupOf_` supest)
      in
        if ok then
          ((var, bool subest supest (subs==[])), [])
        else
          --traceShow (rel, tp1, tp2, sups_ok, ret,tp,insts) $
          --traceShow (sups_ok,grouped) $
          ((var,TypeB),
            if sups_ok && subs_ok && sups/=[] && subs/=[] && (subest `isSubOf` supest) then
              ["type variance does not match : '" ++ show' subest ++
               "' should be supertype of '" ++ show' supest ++ "'"]
            else
              ["ambigous instances for '" ++ var ++ "' : " ++
               intercalate ", " (map (quote.show'.gettp) l)]
          )

    gettp (_,tp,_) = tp
    isSUP (_, _,v) = v == SUP

    quote x = "'" ++ x ++ "'"

    -- the types have no total order but there should be a min
    --sort' :: Bool -> [Type] -> Type
    supest' tps = head $ sortBy (\t1 t2 -> bool GT LT (t1 `isSupOf_` t2)) tps
    subest' tps = head $ sortBy (\t1 t2 -> bool GT LT (t1 `isSubOf` t2)) tps

    comPre' :: [Type] -> [Type]
    comPre' tps = case comPre tps of
                  Just tp   -> tp : tps
                  otherwise -> tps

comPre :: [Type] -> Maybe Type
comPre tps = yyy where
  l = bool [TypeD pre] [] (null tp1s || null pre)

  xxx = find isNotV tps
        where
          isNotV (TypeV _) = False
          isNotV _         = True

  yyy = case xxx of
          Nothing -> bool (Just (head tps)) Nothing (null tps)
          Just tp -> case tp of
            TypeD _       -> case commonPrefixAll $ map (\(TypeD hr)->hr) $ filter isTypeD tps of
                              [] -> Nothing
                              tp -> Just $ TypeD tp
            TypeF inp out -> f $ unzip $ map (\(TypeF inp out)->(inp,out)) $ filter isTypeF tps
                             where
                              f (inps,outs) =
                                case (comPre inps, comPre outs) of
                                  (Just inp, Just out) -> Just $ TypeF inp out
                                  otherwise            -> Nothing

            TypeN ts      -> if all isJust yyy then
                              Just $ TypeN (map fromJust yyy)
                             else
                              Nothing
                             where
                              yyy = map comPre xxx                   -- [ com1,      com2 ]
                              xxx = foldr (zipWith (:)) (rep l) l    -- [ [a,c,...], [b,d,...] ]
                              rep l = assert (ass l) $ replicate (length (head l)) [] -- [ [], [] ]
                              l = map (\(TypeN tps)->tps)            -- [ [a,b], [c,d], ... ]
                                    $ filter isTypeN tps             -- [ tn1,   tn2,   ... ]
                              ass l = and $ map (== head l') (tail l')  -- all lists have same length
                                      where
                                        l' = map length l


            otherwise     -> Nothing

  tp1s = filter isTypeD tps
  pre  = commonPrefixAll $ map (\(TypeD hr)->hr) tp1s

  isTypeD (TypeD _)   = True
  isTypeD _           = False

  isTypeF (TypeF _ _) = True
  isTypeF _           = False

  isTypeN (TypeN _)   = True
  isTypeN _           = False

  -- https://stackoverflow.com/questions/21717646/longest-common-prefix-in-haskell
  commonPrefixAll :: (Eq a) => [[a]] -> [a]
  commonPrefixAll = foldl1 commonPrefix
    where
      commonPrefix :: (Eq e) => [e] -> [e] -> [e]
      commonPrefix _ [] = []
      commonPrefix [] _ = []
      commonPrefix (x:xs) (y:ys)
        | x == y    = x : commonPrefix xs ys
        | otherwise = []

-------------------------------------------------------------------------------

isSupOf :: TypeC -> TypeC -> Bool
isSupOf (sup_,_) (sub_,_) = isSupOf_ sup_ sub_

isSupOf_ :: Type -> Type -> Bool
isSupOf_ sup sub = b where (b,_,_) = sup `supOf` sub

isSubOf :: Type -> Type -> Bool
isSubOf sub sup = b where (b,_,_) = sup `supOf` sub

-- Is first argument a supertype of second argument?
--  * Bool: whether it is or not
--  * Type: most specific type between the two (second argument on success, first otherwise)
--  * list: all instantiations of parametric types [(a,X),(b,Y),(a,X),...]

supOf :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Relation)])
                                        -- "a" >= tp (True)
                                        -- "a" <= tp (False)

supOf TypeT             sub               = (True,  sub,   [])

supOf _                 TypeB             = (True,  TypeB, [])
supOf TypeB             _                 = (False, TypeB, [])

supOf sup@(TypeV a1)    sub@(TypeV a2)    = (True,  sub,   [(a1,sub,SUP),(a2,sup,SUB)])
supOf (TypeV a1)        sub               = (True,  sub,   [(a1,sub,SUP)])
supOf sup               sub@(TypeV a2)    = (True,  sub,   [(a2,sup,SUB)])

supOf Type0             Type0             = (True,  Type0, [])
supOf Type0             _                 = (False, Type0, [])
supOf sup               Type0             = (False, sup,   [])

supOf sup               TypeT             = (False, sup,   [])

supOf sup@(TypeD x)     sub@(TypeD y)
  | x `isPrefixOf` y                      = (True,  sub,   [])
  | otherwise                             = (False, sup,   [])

supOf sup@(TypeD _)     _                 = (False, sup,   [])
supOf sup               (TypeD _)         = (False, sup,   [])

supOf sup@(TypeF inp1 out1) sub@(TypeF inp2 out2) =
  let (i,_,k) = inp2 `supOf` inp1      -- contravariance on inputs
      (x,_,z) = out1 `supOf` out2 in
    if i && x then                           (True,  sub,   k++z)
              else                           (False, sup,   k++z)

supOf sup@(TypeF _ _)   _                 = (False, sup,   [])
supOf sup               (TypeF _ _)       = (False, sup,   [])

supOf sup@(TypeN sups)  (TypeN subs)      = if (length subs) /= (length sups) then
                                              (False, sup, [])
                                            else
                                              foldr f (True, TypeN [], []) $ zipWith supOf sups subs
  where
    f (ret, tp, insts) (ret', TypeN tps', insts') =
      (ret&&ret', TypeN (tp:tps'), insts++insts')

-------------------------------------------------------------------------------

{-
reducesToType0 :: Type -> Bool
reducesToType0 Type0     = True
reducesToType0 (TypeN l) = foldr (\tp acc -> reducesToType0 tp && acc) True l
reducesToType0 _         = False

toTypeN :: Type -> Type
toTypeN (TypeN tps) = TypeN tps
toTypeN Type0       = TypeN []
toTypeN (TypeD tp)  = TypeN [TypeD tp]
toTypeN tp          = error $ show tp
-}
