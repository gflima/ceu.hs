module Ceu.Grammar.Type where

import Control.Exception (assert)
import Data.Bool   (bool)
import Data.Maybe  (fromJust, isJust)
import Data.Either (isRight)
import Data.List   (sort, sortBy, groupBy, find, intercalate, isPrefixOf)
import qualified Data.Set as Set

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints as Cs

data Type = TBot
          | TTop
          | TAny
          | TUnit
          | TData  Bool ID_Data_Hier [Type] --Type    -- X of [Y] with (Y,Int)
          | TTuple [Type]    -- (len >= 2)
          | TFunc  FuncType Type Type
          | TVar   Bool ID_Var
    deriving (Eq,Show)

data Relation = SUP | SUB | ANY | NONE deriving (Eq, Show)

type TypeC = (Type, Cs.Map)

-------------------------------------------------------------------------------

data FuncType = FuncUnknown
              | FuncGlobal    -- cannot access non-locals          // can    be passed and returned
              | FuncNested    -- can    access non-locals          // cannot be passed or  returned
              | FuncClosure   -- can    access non-locals by copy  // can    be passed and returned
                  Int               -- n mem slots, max among all nested FuncClosure
                  --(Set.Set ID_Var)  -- upvalues in asc ID order
                                    -- on enter, (x,z) = EUps
                                    -- on "new", EUps = (x,z)
  deriving (Eq, Show)

type FT_Ups = (FuncType, Maybe (Set.Set (ID_Var,Int)))

ftMin :: FT_Ups -> FT_Ups -> FT_Ups
ftMin (FuncNested,_)          _                       = (FuncNested,    Nothing)
ftMin _                       (FuncNested,_)          = (FuncNested,    Nothing)
ftMin (FuncClosure _, Just x) (FuncClosure _, Just y) = (FuncClosure n, Just s) where
                                                          s = Set.union x y
                                                          n = Set.size s
ftMin (FuncClosure n, Just s) _                       = (FuncClosure n, Just s)
ftMin _                       (FuncClosure n, Just s) = (FuncClosure n, Just s)
ftMin (FuncGlobal,_)    _                             = (FuncGlobal,    Nothing)
ftMin _                 (FuncGlobal,_)                = (FuncGlobal,    Nothing)
ftMin _                 _                             = (FuncUnknown,   Nothing)

-- len  l-1  l-2   ...    0
--   [ locs, lvl1, ..., glbs ]
ftReq :: Int -> (ID_Var,Bool,Int) -> FT_Ups  -- (length, (id,ref,n)
ftReq len (id,ref,n) | (not ref) && n<len-1 && n/=0 = (FuncClosure 1, Just $ Set.singleton (id,n)) -- only non-ref non-local non-global IDs
ftReq len (id,_,  n) | n>=len-1 || n==0 = (FuncGlobal, Nothing)
ftReq _   (_, _,  _)                    = (FuncNested, Nothing)

-------------------------------------------------------------------------------

hier2str = intercalate "."

showC :: TypeC -> String
showC (tp,cs) = case toList cs of
  [] -> show' tp
  l  -> show' tp ++ " where (" ++ intercalate "," (map f l) ++ ")" where
          f (var,[cls]) = var ++ " is " ++ cls
          f (var,clss)  = var ++ " is (" ++ intercalate "," clss ++ ")"

show' :: Type -> String
show' TTop                      = "top"
show' TBot                      = "bot"
show' TAny                      = "?"
show' (TVar   ref id)           = ref2str ref ++ id
show' TUnit                     = "()"
show' (TData  ref hier [] )     = ref2str ref ++ hier2str hier
show' (TData  ref hier [x])     = "(" ++ ref2str ref ++ hier2str hier ++ " of " ++ show' x ++ ")"
show' (TData  ref hier ofs)     = "(" ++ ref2str ref ++ hier2str hier ++ " of " ++ "(" ++ intercalate "," (map show' ofs) ++ ")" ++ ")"
--show' (TFunc  False (FuncClosure _) inp out) = "new (" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TFunc  ft inp out)       = "(" ++ show' inp ++ " -> " ++ show' out ++ ")" ++ (f ft) where
                                    f (FuncClosure _) = "[]"
                                    f _               = ""
show' (TTuple tps)              = "(" ++ intercalate "," (map show' tps) ++ ")"

ref2str True  = "ref "
ref2str False = ""

toTTuple :: Type -> Type
toTTuple tp@(TTuple _) = tp
toTTuple tp            = TTuple [tp]

insTTuple :: Type -> Type -> Type
insTTuple tp (TTuple tup) = TTuple (tp:tup)

listToType :: [Type] -> Type
listToType []    = TUnit
listToType [e]   = e
listToType (e:l) = TTuple (e:l)
--listToType x = error $ show x

-------------------------------------------------------------------------------

{-
isAnyC :: TypeC -> Bool
isAnyC (TAny, _) = True
isAnyC _         = False

isAny :: Type -> Bool
isAny TAny = True
isAny _    = False
-}

isRefableRefC :: TypeC -> Bool
isRefableRefC tpc = isRefableC tpc && isRefC tpc

isRefableC :: TypeC -> Bool
isRefableC (tp,_) = isRefable tp

isRefable :: Type -> Bool
isRefable (TData _ _ _)  = True
isRefable (TVar  _ _  )  = True
isRefable _              = False

isRefC :: TypeC -> Bool
isRefC (tp,cz) = isRef tp

isRef :: Type -> Bool
isRef TUnit             = False
isRef (TData  ref _ _)  = ref
isRef (TTuple _    )    = False
isRef (TFunc  _ _ _)    = False
isRef (TVar   ref _  )  = ref
--isRef _ = False
--isRef x = error $ show x

toRefC :: TypeC -> TypeC
toRefC (tp,cz) = (toRef tp, cz)

toRef :: Type -> Type
toRef (TData  False x y)  = TData  True x y
toRef (TVar   False x  )  = TVar   True x

toDerC :: TypeC -> TypeC
toDerC (tp,cz) = (toDer tp, cz)

toDer :: Type -> Type
toDer (TData  True x y)  = TData  False x y
toDer (TVar   True x  )  = TVar   False x
toDer x = error $ show x

-------------------------------------------------------------------------------

instance Ord Type where
  (<=) TTop                      _                         = True
  (<=) _                         TTop                      = False
  (<=) TBot                      _                         = True
  (<=) _                         TBot                      = False
  (<=) TUnit                     _                         = True
  (<=) _                         TUnit                     = False
  (<=) (TData False h1 ofs1)     (TData False h2 ofs2)     = h1 `isPrefixOf` h2 -- || ofs1>ofs2 || st1>st2
  (<=) (TData False _  _)        _                         = True
  (<=) _                         (TData False _  _)        = False
  (<=) (TFunc _ inp1 out1)       (TFunc _ inp2 out2) = inp1<=inp2 && out1<=out2
  (<=) (TFunc _ _ _)             _                         = True
  (<=) _                         (TFunc _ _ _)             = False
  (<=) (TTuple [])               (TTuple l2)               = True
  (<=) (TTuple l1)               (TTuple [])               = False
  (<=) (TTuple (v1:l1))          (TTuple (v2:l2))| v2<v1     = False
                                                 | v1<v2     = True
                                                 | otherwise = (TTuple l1 <= TTuple l2)
  (<=) (TTuple _)          _                         = True
  (<=) _                         (TTuple _)          = False
  (<=) (TVar False v1)           (TVar False v2)           = v1<=v2

sort' :: [[Type]] -> [[Type]]
sort' ts = map (\(TTuple l)->l) $ sort $ map TTuple ts

-------------------------------------------------------------------------------

getDs :: Type -> [Type]
getDs    TTop                = []
getDs    TBot                = []
getDs    TAny                = []
getDs    (TVar   _ _)        = []
getDs    TUnit               = []
getDs tp@(TData  _ _ ofs)    = [tp] ++ concatMap getDs ofs
getDs    (TFunc  _ inp out)  = getDs inp ++ getDs out
getDs    (TTuple ts)         = concatMap getDs ts

-------------------------------------------------------------------------------

getSuper :: ID_Data_Hier -> Maybe ID_Data_Hier
getSuper [_]  = Nothing
getSuper hier = Just $ (init hier)

-------------------------------------------------------------------------------

-- list: list with instantiated pairs (var,Type)
-- Type: type (possibly TVar) we want to instantiate
-- Type: type of the instantiated variable
-- [(a,TData "Bool"),...] -> TVar "a" -> TData "Bool"
instantiate :: [(ID_Var,Type)] -> Type -> Type
--instantiate x tp | traceShow (x,tp) $ False = TBot
instantiate _    TBot                       = TBot
instantiate _    TUnit                      = TUnit
instantiate vars (TVar   False var)         = case find (\(var',_) -> var==var') vars of
                                                Nothing    -> TVar False var
                                                Just (_,v) -> v
instantiate vars (TData  False hier ofs)    = TData  False hier (map (instantiate vars) ofs) --(instantiate vars st)
instantiate vars (TFunc  ft inp out)        = TFunc  ft (instantiate vars inp) (instantiate vars out)
instantiate vars (TTuple tps)               = TTuple $ map (instantiate vars) tps
--instantiate _ tp = error $ show tp

instantiateC :: [(ID_Var,TypeC)] -> Type -> TypeC
instantiateC vars tp = (instantiate (zip ids tps) tp, cs) where
                        (ids,tpcs) = unzip vars
                        (tps,css)  = unzip tpcs
                        cs = foldr union cz css

-------------------------------------------------------------------------------

isRelC :: Relation -> TypeC -> TypeC -> Bool
isRelC rel (tp1_,_) (tp2_,_) = isRel rel tp1_ tp2_

isRel :: Relation -> Type -> Type -> Bool
isRel rel tp1 tp2 = either (const False) (const True) (relates rel tp1 tp2)

relatesErrorsC :: Relation -> TypeC -> TypeC -> Errors
relatesErrorsC rel (tp1_,_) (tp2_,_) = relatesErrors rel tp1_ tp2_

relatesErrors :: Relation -> Type -> Type -> Errors
relatesErrors rel tp1 tp2 = either id (const []) (relates rel tp1 tp2)

relatesC :: Relation -> TypeC -> TypeC -> Either Errors (TypeC, [(ID_Var,Type)])
relatesC rel (tp1_,cs1) (tp2_,cs2) = -- | (cs1==cs2) = -- TODO: consider cs (depends on REL)
  case relates rel tp1_ tp2_ of
    Left  err        -> Left err
    Right (tp,pairs) -> Right ((tp,cs1), pairs)

relates :: Relation -> Type -> Type -> Either Errors (Type, [(ID_Var,Type)])
relates rel tp1 tp2 =
  if ret && null esi then Right (instantiate right tp, right)
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
    f l@((var,_,_):_) =
      let
          -- input
          sups    = comPre' $ map gettp $ filter isSUP l
          supest  = supest' sups
          sups_ok = all (isSupOf supest) sups

          -- output
          subs    = comPre' $ map gettp $ filter (not.isSUP) l
          subest  = subest' subs
          subs_ok = all (isSubOf subest) subs

          ok      = --traceShow (subs,supest, sups,subest)
                    sups_ok && subs_ok &&
                    (sups==[] || subs==[] || subest `isSupOf` supest)
      in
        if ok then
          ((var, bool subest supest (subs==[])), [])
        else
          --traceShow (rel, tp1, tp2, sups_ok, ret,tp,insts) $
          --traceShow (sups_ok,grouped) $
          ((var,TBot),
            if sups_ok && subs_ok && sups/=[] && subs/=[] && (subest `isSubOf` supest) then
              ["type variance does not match : '" ++ show' subest ++
               "' should be supertype of '" ++ show' supest ++ "'"]
            else
              ["ambiguous implementations for '" ++ var ++ "' : " ++
               intercalate ", " (map (quote.show'.gettp) l)]
          )

    gettp (_,tp,_) = tp
    isSUP (_, _,v) = v == SUP

    quote x = "'" ++ x ++ "'"

    -- the types have no total order but there should be a min
    --sort' :: Bool -> [Type] -> Type
    supest' tps = head $ sortBy (\t1 t2 -> bool GT LT (t1 `isSupOf` t2)) tps
    subest' tps = head $ sortBy (\t1 t2 -> bool GT LT (t1 `isSubOf` t2)) tps

    comPre' :: [Type] -> [Type]
    comPre' tps = case comPre tps of
                  Just tp   -> tp : tps
                  otherwise -> tps

comPre :: [Type] -> Maybe Type
comPre tps = yyy where
  l = bool [TData False pre []] [] (null tp1s || null pre)

  xxx = find isNotV tps
        where
          isNotV (TVar False _) = False
          isNotV _              = True

  yyy = case xxx of
          Nothing -> bool (Just (head tps)) Nothing (null tps)
          Just tp -> case tp of
            TData False _ x  -> case commonPrefixAll $ map (\(TData False hr _)->hr) $ filter isTData tps of
                                    [] -> Nothing
                                    tp -> Just $ TData False tp x
{-
                                    tp -> case comPre $ map (\(TData False _ _ st)->st) $ filter isTData tps of
                                      Nothing  -> Just $ TData False tp x y
                                      Just tp' -> Just $ TData False tp x tp'
-}
            TFunc ft inp out -> f $ unzip $ map (\(TFunc ft inp out)->(inp,out)) $ filter isTFunc tps
                                    where
                                      f (inps,outs) =
                                        case (comPre inps, comPre outs) of
                                          (Just inp, Just out) -> Just $ TFunc ft inp out
                                          otherwise            -> Nothing

            TTuple ts             -> if all isJust yyy then
                                      Just $ TTuple (map fromJust yyy)
                                    else
                                      Nothing
                                    where
                                      yyy = map comPre xxx                   -- [ com1,      com2 ]
                                      xxx = foldr (zipWith (:)) (rep l) l    -- [ [a,c,...], [b,d,...] ]
                                      rep l = assert (ass l) $ replicate (length (head l)) [] -- [ [], [] ]
                                      l = map (\(TTuple tps)->tps)          -- [ [a,b], [c,d], ... ]
                                            $ filter isTTuple tps             -- [ tn1,   tn2,   ... ]
                                      ass l = and $ map (== head l') (tail l')  -- all lists have same length
                                              where
                                                l' = map length l


            otherwise     -> Nothing

  tp1s = filter isTData tps
  pre  = commonPrefixAll $ map (\(TData False hr _)->hr) tp1s

  isTData (TData False _ _)   = True
  isTData _                   = False

  isTFunc (TFunc _ _ _)       = True
  isTFunc _                   = False

  isTTuple (TTuple _)         = True
  isTTuple _                  = False

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

isSupOfC :: TypeC -> TypeC -> Bool
isSupOfC (sup_,_) (sub_,_) = isSupOf sup_ sub_

isSupOf :: Type -> Type -> Bool
isSupOf sup sub = b where (b,_,_) = sup `supOf` sub

isSubOf :: Type -> Type -> Bool
isSubOf sub sup = b where (b,_,_) = sup `supOf` sub

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Is first argument a supertype of second argument?
--  * Bool: whether it is or not
--  * Type: most specific type between the two (second argument on success, first otherwise)
--  * list: all instantiations of parametric types [(a,X),(b,Y),(a,X),...]

supOf :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Relation)])
                                        -- "a" >= tp (True)
                                        -- "a" <= tp (False)

supOf TTop sub  = (True,  sub,  [])
supOf TAny sub  = (True,  sub,  [("?",sub,SUP)])
supOf sup  TAny = (True,  sup,  [("?",sup,SUB)])
supOf _    TBot = (True,  TBot, [])
supOf TBot _    = (False, TBot, [])
supOf sup  TTop = (False, sup,  [])

supOf t1 t2 = if isRef t1 /= isRef t2 then
                (False, t1, [])
              else
                (supOf' t1 t2)

-------------------------------------------------------------------------------

supOf' :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Relation)])

supOf' sup@(TVar False a1) sub@(TVar False a2) = (True,  sub,   [(a1,sub,      SUP),(a2,sup,      SUB)])
supOf' sup@(TVar True  a1) sub@(TVar True  a2) = (True,  sub,   [(a1,toDer sub,SUP),(a2,toDer sup,SUB)])
supOf' (TVar False a1)     sub                 = (True,  sub,   [(a1,sub,      SUP)])
supOf' (TVar True  a1)     sub@(TFunc _ _ _)   = (True,  sub,   [(a1,sub,      SUP)])
supOf' (TVar True  a1)     sub                 = (True,  sub,   [(a1,toDer sub,SUP)])
supOf' sup                 sub@(TVar False a2) = (True,  sup,   [(a2,sup,      SUB)])
supOf' sup                 sub@(TVar True  a2) = (True,  sup,   [(a2,toDer sup,SUB)])

supOf' TUnit               TUnit               = (True,  TUnit, [])
supOf' TUnit               _                   = (False, TUnit, [])
supOf' sup                 TUnit               = (False, sup,   [])

supOf' sup@(TData _ x ofs1) sub@(TData _ y ofs2)
  | not $ x `isPrefixOf` y = (False, sup, [])
  | otherwise              = (ret, TData False x sup', es)
  where
    (ret,TTuple sup',es) = (TTuple ofs1) `supOf'` (TTuple ofs2)
{-
  where
    (ret,sup,es) = f st1 st2

    -- normalize tp1/tp2 to the same length:
    -- data X   with Int
    -- data X.Y with Int
    -- x(_) <- y(_,_)
    f :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Relation)])
    f tp1 tp2 = case tp1 of
      TTuple l1   -> case tp2 of
        TTuple l2 -> (TTuple l1') `supOf` (TTuple l2') where
                            m   = min (length l1) (length l2)
                            l1' = take m l1
                            l2' = take m l2
        TUnit           -> g $ f tp1            (TTuple [])
        _               -> g $ f tp1            (TTuple [tp2])
      TUnit             -> g $ f (TTuple [])    tp2
      _                 -> g $ f (TTuple [tp1]) tp2

    g :: (Bool, Type, [(ID_Var,Type,Relation)]) -> (Bool, Type, [(ID_Var,Type,Relation)])
    g (b, TTuple [],   l) = (b, TUnit, l)
    g (b, TTuple [tp], l) = (b, tp,    l)
    g x                   = x
-}

supOf' sup@(TData False _ _) _                 = (False, sup, [])
supOf' sup                   (TData False _ _) = (False, sup, [])

supOf' sup@(TFunc ft1 inp1 out1) (TFunc ft2 inp2 out2) = (ret, TFunc ft1 inp out, k++z)
  where
    (i,inp,k) = inp2 `supOf` inp1      -- contravariance on inputs
    (x,out,z) = out1 `supOf` out2
    ret = i && x && f ft1 ft2 where
          f (FuncClosure x) (FuncClosure y) = (x >= y)
          f (FuncClosure _) FuncGlobal      = True
          f (FuncClosure _) FuncNested      = False
          f _               _               = True

supOf' sup@(TFunc _ _ _)   _             = (False, sup, [])
supOf' sup                 (TFunc _ _ _) = (False, sup, [])

supOf' sup@(TTuple sups) (TTuple subs) = if (length subs) /= (length sups) then
                                          (False, sup, [])
                                         else
                                          foldr f (True, TTuple [], []) $ zipWith supOf sups subs
  where
    f (ret, tp, insts) (ret', TTuple tps', insts') =
      (ret&&ret', TTuple (tp:tps'), insts++insts')

supOf' x y = error $ show (x,y)
