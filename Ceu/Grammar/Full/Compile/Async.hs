module Ceu.Grammar.Full.Compile.Async where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

-- compile: Adds AwaitAsync in Loops inside Asyncs

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux False p) where
  aux :: Bool -> Stmt -> Stmt
  aux inA   (Var' z id tp Nothing p) = Var' z id tp Nothing (aux inA p)
  aux inA   (Inp' z id b p)       = Inp' z id b (aux inA p)
  aux inA   (Out' z id b p)       = Out' z id b (aux inA p)
  aux inA   (Evt' z id b p)       = Evt' z id b (aux inA p)
  aux inA   (Func' z id tp p)     = Func' z id tp (aux inA p)
  aux inA   (FuncI' z id tp imp p)= FuncI' z id tp (fmap (aux inA) imp) (aux inA p)
  aux inA   (If z exp p1 p2)      = If z exp (aux inA p1) (aux inA p2)
  aux inA   (Seq z p1 p2)         = Seq z (aux inA p1) (aux inA p2)
  aux True  (Loop z p)            = Loop z (aux True (Seq z p (AwaitInp z "ASYNC" Nothing)))
  aux False (Loop z p)            = Loop z (aux False p)
  aux inA   (Par z p1 p2)         = Par z (aux inA p1) (aux inA p2)
  aux inA   (And z p1 p2)         = And z (aux inA p1) (aux inA p2)
  aux inA   (Or z p1 p2)          = Or z (aux inA p1) (aux inA p2)
  aux inA   (Or' z p1 p2)         = Or' z (aux inA p1) (aux inA p2)
  aux inA   (Spawn z p)           = Spawn z (aux inA p)
  aux inA   (Pause z evt p)       = Pause z evt (aux inA p)
  aux inA   (Async _ p)           = (aux True p)
  aux inA   (Trap' z p)           = Trap' z (aux inA p)
  aux inA   p                   = p


