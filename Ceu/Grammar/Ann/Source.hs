{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.Source where

import Ceu.Grammar.Globals (Source, Ann(..))

instance Ann Source where
    getSource src = src
    getN      _   = 0
    getTrails _   = (0,0)
