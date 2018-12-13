module Ceu.Grammar.Full.Compile.Break where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt ann -> (Errors, Stmt ann)
compile p = ([], aux (-1) p)

aux :: Int -> Stmt ann -> Stmt ann
aux n (Var' z var Nothing p) = Var' z var Nothing (aux n p)
aux n (Int' z int b p)       = Int' z int b (aux n p)
aux n (Out' z int b p)       = Out' z int b (aux n p)
aux n (If z exp p1 p2)       = If z exp (aux n p1) (aux n p2)
aux n (Seq z p1 p2)          = Seq z (aux n p1) (aux n p2)
aux n (Loop z p)             = Clean' z "Loop" (Trap' z (Loop z (aux 0 (Trap.ins' p))))
--aux (-1) Break            = error "remBreak: `break` without `loop`"
aux n (Break z)              = Escape' z n
aux n (Every z evt var p)    = Every z evt var (aux n p)
aux n (Par' z p1 p2)         = Par' z (aux n p1) (aux n p2)
aux n (Pause' z var p)       = Pause' z var (aux n p)
aux n (Fin' z p)             = Fin' z (aux n p)
aux n (Trap' z p)            = Trap' z (aux (n+1) p)
aux n (Clean' z id p)        = Clean' z id (aux n p)
aux n p                      = p
