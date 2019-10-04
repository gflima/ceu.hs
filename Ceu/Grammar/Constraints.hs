module Ceu.Grammar.Constraints where

import qualified Data.Map as Map

import Ceu.Grammar.Globals

type Pair = (ID_Var,ID_Class)
type Map  = [(ID_Var, [ID_Class])]

cz = []

cv :: ID_Var -> Map             -- TODO: remove
cv var = [(var, [])]

cvc :: Pair -> Map              -- TODO: remove
cvc (var,cls) = [(var, [cls])]

insert :: Pair -> Map -> Map
insert (var',cls') cs = Map.toList $ Map.insertWith (++) var' [cls'] (Map.fromList cs)

hasClass :: ID_Class -> Map -> Bool
hasClass cls cs = any (elem cls) (map snd cs)

union :: Map -> Map -> Map
union cs1 cs2 = Map.toList $ Map.unionWith (++) (Map.fromList cs1) (Map.fromList cs2)
