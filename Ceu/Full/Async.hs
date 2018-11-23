module Ceu.Full.Async where

import Ceu.Globals
import Ceu.Full.Grammar

-- compile: Adds AwaitFor in Loops inside Asyncs

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux False p) where
  aux :: Bool -> Stmt -> Stmt
  aux inA   (Var id Nothing p) = Var id Nothing (aux inA p)
  aux inA   (Int id b p)       = Int id b (aux inA p)
  aux inA   (If exp p1 p2)     = If exp (aux inA p1) (aux inA p2)
  aux inA   (Seq p1 p2)        = Seq (aux inA p1) (aux inA p2)
  aux True  (Loop p)           = Loop (aux True (Seq p (AwaitExt "ASYNC" Nothing)))
  aux False (Loop p)           = Loop (aux False p)
  aux inA   (Par p1 p2)        = Par (aux inA p1) (aux inA p2)
  aux inA   (And p1 p2)        = And (aux inA p1) (aux inA p2)
  aux inA   (Or p1 p2)         = Or (aux inA p1) (aux inA p2)
  aux inA   (Or' p1 p2)        = Or' (aux inA p1) (aux inA p2)
  aux inA   (Spawn p)          = Spawn (aux inA p)
  aux inA   (Pause evt p)      = Pause evt (aux inA p)
  aux inA   (Async p)          = (aux True p)
  aux inA   (Trap' p)          = Trap' (aux inA p)
  aux inA   p                  = p


