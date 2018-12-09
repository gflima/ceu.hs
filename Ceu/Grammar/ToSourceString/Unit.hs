module Ceu.Grammar.ToSourceString.Unit where

import Ceu.Grammar.Globals (ToSourceString(..))

instance ToSourceString () where
    toSourceString () = ""
