module Ceu.Grammar.Ann.Unit where

import Ceu.Grammar.Globals (Ann(..))

instance Ann () where
    toSourceString () = ""
    toN _ = 0
