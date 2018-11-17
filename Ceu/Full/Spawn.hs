module Ceu.Full.Spawn where

import Ceu.Full.Grammar

-- remove: Converts (spawn p1; ...) into (p1;AwaitFor or ...)

remove :: Stmt -> Stmt
remove (Var id Nothing p)  = Var id Nothing (remove p)
remove (Int id b p)        = Int id b (remove p)
remove (If exp p1 p2)      = If exp (remove p1) (remove p2)
remove (Seq (Spawn p1) p2) = Or (Seq (remove p1) AwaitFor) (remove p2)
remove (Seq p1 p2)         = Seq (remove p1) (remove p2)
remove (Loop p)            = Loop (remove p)
remove (And p1 p2)         = And (remove p1) (remove p2)
remove (Or p1 p2)          = Or (remove p1) (remove p2)
remove (Spawn p)           = error "remSpawn: unexpected statement (Spawn)"
remove (Pause' var p)      = Pause' var (remove p)
remove p                   = p

-- check: `Spawn` can only appear as first item in `Seq`

check :: Stmt -> Stmt
check p = case p of
  (Spawn _) -> error "chkSpawn: unexpected statement (Spawn)"
  _ | (chkS p) -> p
    | otherwise -> error "chkSpawn: unexpected statement (Spawn)"
  where

  notS (Spawn _) = False
  notS p         = True

  chkS :: Stmt -> Bool
  chkS (Var _ _ p)   = (notS p) && (chkS p)
  chkS (Int _ _ p)   = (notS p) && (chkS p)
  chkS (If _ p1 p2)  = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Seq p1 p2)   = (chkS p1) && (notS p2) && (chkS p2)
  chkS (Loop p)      = (notS p) && (chkS p)
  chkS (Every _ _ p) = (notS p) && (chkS p)
  chkS (And p1 p2)   = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Or p1 p2)    = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Spawn p)     = (notS p) && (chkS p)
  chkS (Pause' _ p)  = (notS p)
  chkS (Fin' p)      = (notS p) && (chkS p)
  chkS (Async p)     = (notS p) && (chkS p)
  chkS _             = True
