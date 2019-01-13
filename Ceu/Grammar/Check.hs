module Ceu.Grammar.Check where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann(..), errs_anns_msg_map, toError, getAnn)
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Stmt     (Stmt(..))
import qualified Ceu.Grammar.TypeSys as TypeSys

-------------------------------------------------------------------------------

type Options = (Bool)

prelude z p = (Data z "Int" [] [] False p)

compile :: Options -> Stmt -> (Errors, Stmt)
compile (o_prel) p = (es2,p2) where
  p1       = if not o_prel then p else prelude z p
  (es2,p2) = TypeSys.go p1
  z        = getAnn p
