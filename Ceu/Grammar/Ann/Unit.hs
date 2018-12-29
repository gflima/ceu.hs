module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Type (Type(..))
import Ceu.Grammar.Ann  (Ann(..))

instance Ann () where
    getType   _   = TypeB
    getName   _   = ""
    getSource _   = ("",0,0)
    getN      _   = 0
    getTrails _   = (0,0)
