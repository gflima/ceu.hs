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
toList ctrs = map (\(x,y) -> (x,Set.toList y)) $ Map.toList ctrs

insert :: Pair -> Map -> Map
insert (var',cls') ctrs = Map.insertWith Set.union var' (Set.singleton cls') ctrs

hasClass :: ID_Class -> Map -> Bool
hasClass cls ctrs = any (Set.member cls) (Map.elems ctrs)

union :: Map -> Map -> Map
union ctrs1 ctrs2 = Map.unionWith Set.union ctrs1 ctrs2
