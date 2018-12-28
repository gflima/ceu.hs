--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.All where

import Ceu.Grammar.Globals (Source, Trails, Ann(..))

data All = All { source :: Source
               , n      :: Int
               , trails :: Trails
               }
    deriving (Eq, Show)

instance Ann All where
    getSource v = source v
    getN      v = n v
    getTrails v = trails v
