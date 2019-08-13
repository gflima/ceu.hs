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
          | TUnit  Bool
          | TData  Bool ID_Data_Hier [Type] Type    -- X of [Y] with (Y,Int)
          | TTuple Bool [Type]    -- (len >= 2)
          | TFunc  Bool FuncType Type Type
          | TVar   Bool ID_Var
    deriving (Eq,Show)

data Relation = SUP | SUB | ANY | NONE deriving (Eq, Show)

type TypeC = (Type, Cs.Map)

-------------------------------------------------------------------------------

data FuncType = FuncUnknown
              | FuncGlobal    -- cannot access non-locals             // can    be passed and returned
              | FuncNested    -- can    access non-locals             // cannot be passed or  returned
              | FuncCloseBody -- can    access non-local args by ref  // can    be passed and returned
                  (Set.Set ID_Var)  -- upvalues in asc ID order
                                    -- on enter, (x,z) = EUps
              | FuncCloseOuter
                  Int               -- n mem slots, max among all nested FuncCloseBody
                                    -- on "new", EUps = (x,z)
              | FuncCloseCall
                  Int Int           -- n mem slots // max upvs scope depth
  deriving (Eq, Show)

ftMin :: FuncType -> FuncType -> FuncType
ftMin FuncNested        _                 = FuncNested
ftMin _                 FuncNested        = FuncNested
ftMin (FuncCloseBody x) (FuncCloseBody y) = FuncCloseBody $ Set.union x y
ftMin (FuncCloseBody x) _                 = FuncCloseBody x
ftMin _                 (FuncCloseBody y) = FuncCloseBody y
ftMin FuncGlobal        _                 = FuncGlobal
ftMin _                 FuncGlobal        = FuncGlobal
ftMin _                 _                 = FuncUnknown

-- len  l-1  l-2   l-3  l-4  ...    1    0
--   [ locs,args, lvl1,args, ..., glbs,args ]
ftReq :: Int -> (ID_Var,Bool,Int) -> FuncType  -- (length, (id,ref,n)
ftReq len (id,ref,n) | ref && n==len-4  = FuncCloseBody $ Set.singleton id -- only non-local args by ref
ftReq len (_,_,   n) | n>=len-2 || n<=1 = FuncGlobal
ftReq _   _                             = FuncNested

-------------------------------------------------------------------------------

hier2str = intercalate "."

show' :: Type -> String
show' TTop                      = "top"
show' TBot                      = "bot"
show' TAny                      = "?"
show' (TVar   ref id)           = ref2str ref ++ id
show' (TUnit  False)            = "()"
show' (TData  ref hier []  _)   = ref2str ref ++ hier2str hier
show' (TData  ref hier [x] _)   = "(" ++ ref2str ref ++ hier2str hier ++ " of " ++ show' x ++ ")"
show' (TData  ref hier ofs _)   = "(" ++ ref2str ref ++ hier2str hier ++ " of " ++ "(" ++ intercalate "," (map show' ofs) ++ ")" ++ ")"
--show' (TFunc  False (FuncClosure _) inp out) = "new (" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TFunc  ref _ inp out)    = ref2str ref ++ "(" ++ show' inp ++ " -> " ++ show' out ++ ")"
show' (TTuple False tps)        = "(" ++ intercalate "," (map show' tps) ++ ")"

ref2str True  = "ref "
ref2str False = ""

-------------------------------------------------------------------------------

isAnyC :: TypeC -> Bool
isAnyC (TAny, _) = True
isAnyC _         = False

isRefC :: TypeC -> Bool
isRefC (tp,cz) = isRef tp

isRef :: Type -> Bool
isRef (TUnit  ref      )  = ref
isRef (TData  ref _ _ _)  = ref
isRef (TTuple ref _    )  = ref
isRef (TFunc  ref _ _ _)  = ref
isRef (TVar   ref _    )  = ref
--isRef _ = False
--isRef x = error $ show x

toRefC :: TypeC -> TypeC
toRefC (tp,cz) = (toRef tp, cz)

toRef :: Type -> Type
toRef (TUnit  False      )  = TUnit  True
toRef (TData  False x y z)  = TData  True x y z
toRef (TTuple False x    )  = TTuple True x
toRef (TFunc  False x y z)  = TFunc  True x y z
toRef (TVar   False x    )  = TVar   True x

toDerC :: TypeC -> TypeC
toDerC (tp,cz) = (toDer tp, cz)

toDerC' :: TypeC -> TypeC
toDerC' tpc = bool tpc (toDerC tpc) ((not $ isAnyC tpc) && isRefC tpc)

toDer :: Type -> Type
toDer (TUnit  True      )  = TUnit  False
toDer (TData  True x y z)  = TData  False x y z
toDer (TTuple True x    )  = TTuple False x
toDer (TFunc  True x y z)  = TFunc  False x y z
toDer (TVar   True x    )  = TVar   False x
--toDer x = error $ show x

-------------------------------------------------------------------------------

instance Ord Type where
  (<=) TTop                      _                         = True
  (<=) _                         TTop                      = False
  (<=) TBot                      _                         = True
  (<=) _                         TBot                      = False
  (<=) (TUnit False)             _                         = True
  (<=) _                         (TUnit False)             = False
  (<=) (TData False h1 ofs1 st1) (TData False h2 ofs2 st2) = h1 `isPrefixOf` h2 -- || ofs1>ofs2 || st1>st2
  (<=) (TData False _  _    _)   _                         = True
  (<=) _                         (TData False _  _    _)   = False
  (<=) (TFunc False _ inp1 out1) (TFunc False _ inp2 out2) = inp1<=inp2 && out1<=out2
  (<=) (TFunc False _ _    _)    _                         = True
  (<=) _                         (TFunc _ _ _ _)           = False
  (<=) (TTuple False [])         (TTuple False l2)         = True
  (<=) (TTuple False l1)         (TTuple False [])         = False
  (<=) (TTuple False (v1:l1))    (TTuple False (v2:l2))| v2<v1 = False
                                               | v1<v2     = True
                                               | otherwise = (TTuple False l1 <= TTuple False l2)
  (<=) (TTuple False _)          _                         = True
  (<=) _                         (TTuple False _)          = False
  (<=) (TVar False v1)           (TVar False v2)           = v1<=v2

sort' :: [[Type]] -> [[Type]]
sort' ts = map (\(TTuple False l)->l) $ sort $ map (TTuple False) ts

-------------------------------------------------------------------------------

getDs :: Type -> [Type]
getDs    TTop                = []
getDs    TBot                = []
getDs    TAny                = []
getDs    (TVar   _ _)        = []
getDs    (TUnit  _)          = []
getDs tp@(TData  _ _ ofs st) = [tp] ++ concatMap getDs ofs ++ getDs st
getDs    (TFunc  _ _ inp out) = getDs inp ++ getDs out
getDs    (TTuple _ ts)       = concatMap getDs ts

-------------------------------------------------------------------------------

getSuper :: ID_Data_Hier -> Maybe ID_Data_Hier
getSuper [_]  = Nothing
getSuper hier = Just $ (init hier)

splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d [] = []
splitOn d s = x : splitOn d (drop 1 y) where (x,y) = span (/= d) s

-------------------------------------------------------------------------------

-- list: list with instantiated pairs (var,Type)
-- Type: type (possibly TVar) we want to instantiate
-- Type: type of the instantiated variable
-- [(a,TData "Bool"),...] -> TVar "a" -> TData "Bool"
instantiate :: [(ID_Var,Type)] -> Type -> Type
instantiate vars (TVar   False var)         = case find (\(var',_) -> var==var') vars of
                                                Nothing    -> TVar False var
                                                Just (_,v) -> v
instantiate vars (TData  False hier ofs st) = TData  False hier (map (instantiate vars) ofs) (instantiate vars st)
instantiate vars (TFunc  False ft inp out)  = TFunc  False ft (instantiate vars inp) (instantiate vars out)
instantiate vars (TTuple False tps)         = TTuple False $ map (instantiate vars) tps
instantiate _    tp                         = tp

-------------------------------------------------------------------------------

isRelC :: Relation -> TypeC -> TypeC -> Bool
isRelC rel (tp1_,_) (tp2_,_) = isRel rel tp1_ tp2_

isRel :: Relation -> Type -> Type -> Bool
isRel rel tp1 tp2 = either (const False) (const True) (relates rel tp1 tp2)

relatesErrorsC :: Relation -> TypeC -> TypeC -> Errors
relatesErrorsC rel (tp1_,_) (tp2_,_) = relatesErrors rel tp1_ tp2_

relatesErrors :: Relation -> Type -> Type -> Errors
relatesErrors rel tp1 tp2 = either id (const []) (relates rel tp1 tp2)

-- TODO: relates deve levar em consideracao os ctrs (e depende da REL)
relatesC :: Relation -> TypeC -> TypeC -> Either Errors (Type, [(ID_Var,Type)])
relatesC rel (tp1_,_) (tp2_,_) = relates rel tp1_ tp2_

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
              ["ambiguous instances for '" ++ var ++ "' : " ++
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
  l = bool [TData False pre [] (TUnit False)] [] (null tp1s || null pre)

  xxx = find isNotV tps
        where
          isNotV (TVar False _) = False
          isNotV _              = True

  yyy = case xxx of
          Nothing -> bool (Just (head tps)) Nothing (null tps)
          Just tp -> case tp of
            TData False _ x y   -> case commonPrefixAll $ map (\(TData False hr _ _)->hr) $ filter isTData tps of
                                    [] -> Nothing
{-
                                    tp -> Just $ TData tp x y
-}
                                    tp -> case comPre $ map (\(TData False _ _ st)->st) $ filter isTData tps of
                                      Nothing  -> Just $ TData False tp x y
                                      Just tp' -> Just $ TData False tp x tp'
            TFunc False ft inp out -> f $ unzip $ map (\(TFunc False ft inp out)->(inp,out)) $ filter isTFunc tps
                                    where
                                      f (inps,outs) =
                                        case (comPre inps, comPre outs) of
                                          (Just inp, Just out) -> Just $ TFunc False ft inp out
                                          otherwise            -> Nothing

            TTuple False ts      -> if all isJust yyy then
                                      Just $ TTuple False (map fromJust yyy)
                                    else
                                      Nothing
                                    where
                                      yyy = map comPre xxx                   -- [ com1,      com2 ]
                                      xxx = foldr (zipWith (:)) (rep l) l    -- [ [a,c,...], [b,d,...] ]
                                      rep l = assert (ass l) $ replicate (length (head l)) [] -- [ [], [] ]
                                      l = map (\(TTuple False tps)->tps)          -- [ [a,b], [c,d], ... ]
                                            $ filter isTTuple tps             -- [ tn1,   tn2,   ... ]
                                      ass l = and $ map (== head l') (tail l')  -- all lists have same length
                                              where
                                                l' = map length l


            otherwise     -> Nothing

  tp1s = filter isTData tps
  pre  = commonPrefixAll $ map (\(TData False hr _ _)->hr) tp1s

  isTData (TData False _ _ _) = True
  isTData _                   = False

  isTFunc (TFunc False _ _ _) = True
  isTFunc _                   = False

  isTTuple (TTuple False _)   = True
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

supOf' sup@(TVar _ a1)     sub@(TVar _ a2)     = (True,  sub,         [(a1,sub,SUP),(a2,sup,SUB)])
supOf' (TVar _ a1)         sub                 = (True,  sub,         [(a1,sub,SUP)])
supOf' sup                 sub@(TVar _ a2)     = (True,  sup,         [(a2,sup,SUB)])

supOf' (TUnit False)       (TUnit False)       = (True,  TUnit False, [])
supOf' (TUnit False)       _                   = (False, TUnit False, [])
supOf' sup                 (TUnit False)       = (False, sup,         [])

supOf' sup@(TData _ x ofs1 st1) sub@(TData _ y ofs2 st2)
  | not $ x `isPrefixOf` y = (False, sup,   [])
  | not $ (TTuple False ofs1) `isSupOf` (TTuple False ofs2) = (False, sup,   [])
  | otherwise              = (ret, TData False x ofs1 sup, es)
  where
    (ret,sup,es) = f st1 st2

    -- normalize tp1/tp2 to the same length:
    -- data X   with Int
    -- data X.Y with Int
    -- x(_) <- y(_,_)
    f :: Type -> Type -> (Bool, Type, [(ID_Var,Type,Relation)])
    f tp1 tp2 = case tp1 of
      TTuple False l1   -> case tp2 of
        TTuple False l2 -> (TTuple False l1') `supOf` (TTuple False l2') where
                            m   = min (length l1) (length l2)
                            l1' = take m l1
                            l2' = take m l2
        TUnit False     -> g $ f tp1                  (TTuple False [])
        _               -> g $ f tp1                  (TTuple False [tp2])
      TUnit False       -> g $ f (TTuple False [])    tp2
      _                 -> g $ f (TTuple False [tp1]) tp2

    g :: (Bool, Type, [(ID_Var,Type,Relation)]) -> (Bool, Type, [(ID_Var,Type,Relation)])
    g (b, TTuple False [],   l) = (b, TUnit False, l)
    g (b, TTuple False [tp], l) = (b, tp,          l)
    g x                     = x

supOf' sup@(TData False _ _ _) _                   = (False, sup,   [])
supOf' sup                     (TData False _ _ _) = (False, sup,   [])

supOf' sup@(TFunc ref1 ft1 inp1 out1) (TFunc _ ft2 inp2 out2)
  | otherwise    = (ret, TFunc ref1 ft inp out, k++z) where
    ft = ft1 --case traceShowId (sup,sub) of (_,_) | ft1==ft2 -> ft1
    (i,inp,k) = inp2 `supOf` inp1      -- contravariance on inputs
    (x,out,z) = out1 `supOf` out2
    ret = i && x

supOf' sup@(TFunc _ _ _ _)   _               = (False, sup,   [])
supOf' sup                   (TFunc _ _ _ _) = (False, sup,   [])

supOf' sup@(TTuple False sups) (TTuple False subs) = if (length subs) /= (length sups) then
                                                      (False, sup, [])
                                                     else
                                                      foldr f (True, TTuple False [], []) $ zipWith supOf sups subs
  where
    f (ret, tp, insts) (ret', TTuple False tps', insts') =
      (ret&&ret', TTuple False (tp:tps'), insts++insts')

supOf' x y = error $ show (x,y)
