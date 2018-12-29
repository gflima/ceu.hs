--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.All where

import Ceu.Grammar.Globals (Source, Trails)
import Ceu.Grammar.Ann     (Ann(..))
import Ceu.Grammar.Type    (Type(..))


data All = All { source :: Source
               , n      :: Int
               , trails :: Trails
               }
    deriving (Eq, Show)

instance Ann All where
    getType   _ = TypeB
    getName   _ = ""
    getSource v = source v
    getN      v = n v
    getTrails v = trails v
