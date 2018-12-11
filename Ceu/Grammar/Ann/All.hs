--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.All where

import Ceu.Grammar.Globals (Source, Ann(..))

data All = All { n      :: Int
               , source :: Source
               }

instance Ann All where
    getSource (All _ src) = Just src
    getN v = (n v)
