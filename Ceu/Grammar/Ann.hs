module Ceu.Grammar.Ann where

import Data.Bool                (bool)
import Debug.Trace

import Ceu.Grammar.Globals      (Source, Errors)
import Ceu.Grammar.Type         (Type(TBot),TypeC)
import Ceu.Grammar.Constraints  (cz)

data Ann = Ann { typec  :: TypeC
               , name   :: String
               , source :: Source
               , nn     :: Int
               }
    deriving (Eq, Show)

class HasAnn a where
    getAnn :: a -> Ann

annz :: Ann
annz = Ann { typec  = (TBot,cz)
           , name   = ""
           , source = ("",0,0)
           , nn     = (-1)
           }

toErrors' :: Ann -> String -> String -> [String]
toErrors' z id msg = bool (toErrors z msg) [] $ elem '$' id

toErrors :: Ann -> String -> [String]
toErrors z msg = [toError z msg]

toError :: Ann -> String -> String
toError z msg = src ++ pre ++ msg where
    pre = let nm=name z in if nm=="" then "" else ": "
    src = case source z of
        (_,0, 0)  -> ""
        (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

errs_anns_msg_map :: [Ann] -> String -> Errors
errs_anns_msg_map zs msg = map (\z -> (let nm=name z in if nm=="" then "" else nm++": ")
                                      ++ msg) zs
