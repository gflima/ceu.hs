module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Ann  (Ann(..))
import Ceu.Grammar.Type (Type(..))

instance Ann () where
    getName   _   = ""
    getType   _   = TypeB
    getSource _   = ("",0,0)
    getN      _   = 0
    getTrails _   = (0,0)
