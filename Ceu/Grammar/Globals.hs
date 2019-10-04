module Ceu.Grammar.Globals where

import Data.List (intercalate)

type Errors = [String]

type Source = (String, Int, Int)    -- filename, line, column

type ID_Var       = String
type ID_Class     = String
type ID_Data      = String
type ID_Data_Hier = [ID_Data]

id2 _ x = x
f2 f _ x  = f x

dol  id  = dols [id]
dols ids = "$" ++ intercalate "$" ids ++ "$"

-- All possible combinations between members of each group:
--    G1        G2        G3
-- [ [1,10], [2,20,200], [3], ... ]
-- [ [1,2,3,...], [1,20,3,...], [1,200,3,...], ... ]
combos :: [[a]] -> [[a]]
combos l = foldr g [[]] l where
    g :: [a] -> [[a]] -> [[a]]
    g l combos = foldr (\v acc -> (h v combos) ++ acc) [] l

    h :: a -> [[a]] -> [[a]]
    h v combos = map (\combo -> v:combo) combos

splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d [] = []
splitOn d s = x : splitOn d (drop 1 y) where (x,y) = span (/= d) s
