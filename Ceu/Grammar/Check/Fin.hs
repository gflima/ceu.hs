module Ceu.Grammar.Check.Fin where

import Ceu.Grammar

-- Receives a Fin or Every statement and checks whether it does not contain
-- any occurrences of Loop/Break/Await*/Every/Fin.
check :: Stmt -> Bool
check finOrEvery = case finOrEvery of
  Fin body     -> cF body
  Every _ body -> cF body
  _            -> error "checkFin: expected Fin or Every"
  where
    cF stmt = case stmt of
      AwaitInt _   -> False
      AwaitExt _   -> False
      Every _ _    -> False
      Fin _        -> False
      Loop _       -> False
      Var _ p      -> cF p
      Int _ p      -> cF p
      If _ p q     -> cF p && cF q
      Seq p q      -> cF p && cF q
      Par p q      -> cF p && cF q
      Pause _ p    -> cF p
      Trap p       -> cF p
      Escape _     -> False
      _            -> True
