module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Globals (Ann(..))

instance Ann () where
    getSource () = Nothing
    getN _ = 0
