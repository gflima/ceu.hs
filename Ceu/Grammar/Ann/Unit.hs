module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Globals (Ann(..))

instance Ann () where
    getSource () = ""
    getN _ = 0
