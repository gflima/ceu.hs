module Ceu.Grammar.Ann where

import Debug.Trace

import Ceu.Grammar.Globals (Source, Errors)
import Ceu.Grammar.Type    (Type(TypeB),TypeC, cz)

data Ann = Ann { type_  :: TypeC
               , name   :: String
               , source :: Source
               , nn     :: Int
               }
    deriving (Eq, Show)

class HasAnn a where
    getAnn :: a -> Ann

annz :: Ann
annz = Ann { type_  = (TypeB,cz)
           , name   = ""
           , source = ("",0,0)
           , nn     = (-1)
           }

toError  :: Ann -> String -> String
toError z msg = src ++ pre ++ msg where
    pre = let nm=name z in if nm=="" then "" else ": "
    src = case source z of
        (_,0, 0)  -> ""
        (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

errs_anns_msg_map :: [Ann] -> String -> Errors
errs_anns_msg_map zs msg = map (\z -> (let nm=name z in if nm=="" then "" else nm++": ")
                                      ++ msg) zs
