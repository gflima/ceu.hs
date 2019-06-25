module Ceu.Grammar.Type where

import Control.Exception (assert)
import Debug.Trace
import Data.Bool   (bool)
import Data.Maybe  (fromJust, isJust)
import Data.Either (isRight)
import Data.List   (sortBy, groupBy, find, intercalate, isPrefixOf)
import qualified Data.Set as Set

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints as Cs

data Type = TypeB
          | TypeT
          | Type0
          | TypeD ID_Data_Hier Type
          | TypeN [Type]    -- (len >= 2)
          | TypeF Type Type
          | TypeV ID_Var
    deriving (Eq,Show)

data Relation = SUP | SUB | ANY | NONE deriving (Eq, Show)

type TypeC = (Type, Cs.Map)

-------------------------------------------------------------------------------

hier2str = intercalate "."

show' :: Type -> String
show' (TypeV id)         = id
show' TypeT              = "top"
show' TypeB              = "bot"
show' Type0              = "()"
show' (TypeD hier Type0) = hier2str hier
show' (TypeD hier tp)    = "(" ++ hier2str hier ++ " " ++ show' tp ++ ")"
show' (TypeF inp out)    = "(" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TypeN tps)        = "(" ++ intercalate "," (map show' tps) ++ ")"

-------------------------------------------------------------------------------

getDs :: Type -> [Type]

getDs (TypeV _)       = []
getDs TypeT           = []
getDs TypeB           = []
getDs Type0           = []
getDs tp@(TypeD _ _)  = [tp]
getDs (TypeF inp out) = (getDs inp) ++ (getDs out)
getDs (TypeN ts)      = concatMap getDs ts

-------------------------------------------------------------------------------

getSuper :: ID_Data_Hier -> Maybe ID_Data_Hier
getSuper [_]  = Nothing
getSuper hier = Just $ (init hier)

splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d [] = []
splitOn d s = x : splitOn d (drop 1 y) where (x,y) = span (/= d) s

-------------------------------------------------------------------------------

-- list: list with instantiated pairs (var,Type)
-- Type: type (possibly TypeV) we want to instantiate
-- Type: type of the instantiated variable
-- [(a,TypeD "Bool"),...] -> TypeV "a" -> TypeD "Bool"
instantiate :: [(ID_Var,Type)] -> Type -> Type
instantiate vars (TypeV var)    = case find (\(var',_) -> var==var') vars of
                                    Nothing    -> TypeV var
                                    Just (_,v) -> v
instantiate vars (TypeD hier tp) = TypeD hier (instantiate vars tp)
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
  l = bool [TypeD pre Type0] [] (null tp1s || null pre)

  xxx = find isNotV tps
        where
          isNotV (TypeV _) = False
          isNotV _         = True

  yyy = case xxx of
          Nothing -> bool (Just (head tps)) Nothing (null tps)
          Just tp -> case tp of
            TypeD _ x     -> case commonPrefixAll $ map (\(TypeD hr _)->hr) $ filter isTypeD tps of
                              [] -> Nothing
                              tp -> Just $ TypeD tp x
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
  pre  = commonPrefixAll $ map (\(TypeD hr _)->hr) tp1s

  isTypeD (TypeD _ _) = True
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

supOf sup@(TypeD x tp1) sub@(TypeD y tp2)
  | x `isPrefixOf` y && tp1 `sup'` tp2    = (True,  sub,   [])
  -- | x `isPrefixOf` y                      = (True,  sub,   [])
  | otherwise                             = (False, sup,   [])
  where
    -- normalize tp1/tp2 to the same length:
    -- data X   with Int
    -- data X.Y with Int
    -- x(_) <- y(_,_)
    sup' :: Type -> Type -> Bool
    sup' tp1 tp2 = case tp1 of
      TypeN l1   -> case tp2 of
        TypeN l2 -> (TypeN l1') `isSupOf_` (TypeN l2') where
                      m   = min (length l1) (length l2)
                      l1' = take m l1
                      l2' = take m l2
        Type0    -> sup' tp1           (TypeN [])
        _        -> sup' tp1           (TypeN [tp2])
      Type0      -> sup' (TypeN [])    tp2
      _          -> sup' (TypeN [tp1]) tp2

supOf sup@(TypeD _ _)   _                 = (False, sup,   [])
supOf sup               (TypeD _ _)       = (False, sup,   [])

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
