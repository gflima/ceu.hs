module Ceu.Full.Async where

import Ceu.Full.Grammar

-- remove: Adds AwaitFor in Loops inside Asyncs

remove :: Stmt -> Stmt
remove p = (rA False p) where
  rA :: Bool -> Stmt -> Stmt
  rA inA   (Var id Nothing p) = Var id Nothing (rA inA p)
  rA inA   (Int id b p)       = Int id b (rA inA p)
  rA inA   (If exp p1 p2)     = If exp (rA inA p1) (rA inA p2)
  rA inA   (Seq p1 p2)        = Seq (rA inA p1) (rA inA p2)
  rA True  (Loop p)           = Loop (rA True (Seq p (AwaitExt "ASYNC" Nothing)))
  rA False (Loop p)           = Loop (rA False p)
  rA inA   (And p1 p2)        = And (rA inA p1) (rA inA p2)
  rA inA   (Or p1 p2)         = Or (rA inA p1) (rA inA p2)
  rA inA   (Spawn p)          = Spawn (rA inA p)
  rA inA   (Pause evt p)      = Pause evt (rA inA p)
  rA inA   (Async p)          = (rA True p)
  rA inA   p                  = p


