{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.Source where

import Ceu.Grammar.Globals (Source)
import Ceu.Grammar.Type    (Type(..))
import Ceu.Grammar.Ann     (Ann(..))

instance Ann Source where
    getType   _   = TypeB
    getName   _   = ""
    getSource src = src
    getN      _   = 0
    getTrails _   = (0,0)
