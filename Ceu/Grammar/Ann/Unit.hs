module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Globals (Ann(..))

instance Ann () where
    getSource _ = Nothing
    getN      _ = 0
    getTrails _ = (0,0)
