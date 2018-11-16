module Ceu.Grammar.Check.Every where

import Ceu.Grammar
import qualified Ceu.Grammar.Check.Fin as Fin

-- Alias for checkFin.
check :: Stmt -> Bool
check = Fin.check
