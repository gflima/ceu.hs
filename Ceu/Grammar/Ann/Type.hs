{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceu.Grammar.Ann.Type where

import Ceu.Grammar.Type (Type(..))
import Ceu.Grammar.Ann  (Ann(..))

instance Ann Type where
    getType   tp  = tp
    getName   _   = ""
    getSource _   = ("",0,0)
    getN      _   = 0
    getTrails _   = (0,0)
