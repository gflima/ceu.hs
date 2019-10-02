module Ceu.Grammar.Constraints where

import qualified Data.Set as Set
import qualified Data.Map as Map

import Ceu.Grammar.Globals

type Pair = (ID_Var,ID_Class)
type Map  = Map.Map ID_Var (Set.Set ID_Class)

cz = Map.empty
cv :: ID_Var -> Map
cv var = Map.singleton var Set.empty
cvc :: Pair -> Map
cvc (var,cls) = Map.singleton var $ Set.singleton cls

toList :: Map -> [(ID_Var,[ID_Class])]
toList cs = map (\(x,y) -> (x,Set.toList y)) $ Map.toList cs

insert :: Pair -> Map -> Map
insert (var',cls') cs = Map.insertWith Set.union var' (Set.singleton cls') cs

hasClass :: ID_Class -> Map -> Bool
hasClass cls cs = any (Set.member cls) (Map.elems cs)

union :: Map -> Map -> Map
union cs1 cs2 = Map.unionWith Set.union cs1 cs2
