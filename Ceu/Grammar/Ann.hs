module Ceu.Grammar.Ann where

import Debug.Trace
import Ceu.Grammar.Globals (Source, Trails, Errors)
import Ceu.Grammar.Type    (Type(TypeB))

data Ann = Ann { isInst :: Bool     -- TODO
               , type_  :: Type
               , name   :: String
               , source :: Source
               , nn     :: Int
               , trails :: Trails
               }
    deriving (Eq, Show)

class HasAnn a where
    getAnn :: a -> Ann

annz :: Ann
annz = Ann { isInst = True
           , type_  = TypeB
           , name   = ""
           , source = ("",0,0)
           , nn     = (-1)
           , trails = (0,0)
           }

toError  :: Ann -> String -> String
toError z msg = src ++ pre ++ msg where
    pre = let nm=name z in if nm=="" then "" else ": "
    src = case source z of
        (_,0, 0)  -> ""
        (_,ln,cl) -> "(line " ++ (show ln) ++ ", column " ++ (show cl) ++ "):\n"

toTrails0 :: Ann -> Int
toTrails0 = fst . trails
toTrailsN :: Ann -> Int
toTrailsN = snd . trails

errs_anns_msg_map :: [Ann] -> String -> Errors
errs_anns_msg_map zs msg = map (\z -> (let nm=name z in if nm=="" then "" else nm++": ")
                                      ++ msg) zs
