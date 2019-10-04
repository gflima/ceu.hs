module Ceu.Grammar.Constraints where

import qualified Data.Map as Map

import Ceu.Grammar.Globals

type Pair = (ID_Var,ID_Class)
type Map  = Map.Map ID_Var [ID_Class]

cz = Map.empty
cv :: ID_Var -> Map
cv var = Map.singleton var []
cvc :: Pair -> Map
cvc (var,cls) = Map.singleton var [cls]

toList :: Map -> [(ID_Var,[ID_Class])]
toList cs = Map.toList cs

insert :: Pair -> Map -> Map
insert (var',cls') cs = Map.insertWith (++) var' [cls'] cs

hasClass :: ID_Class -> Map -> Bool
hasClass cls cs = any (elem cls) (Map.elems cs)

union :: Map -> Map -> Map
union cs1 cs2 = Map.unionWith (++) cs1 cs2
