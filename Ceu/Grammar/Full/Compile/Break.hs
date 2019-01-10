module Ceu.Grammar.Full.Compile.Break where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Stmt
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux (-1) p)

aux :: Int -> Stmt -> Stmt
aux n (Data' z tp vars cons abs p) = Data' z tp vars cons abs (aux n p)
aux n (Var' z var tp Nothing p) = Var' z var tp Nothing (aux n p)
aux n (Inp' z int tp p)      = Inp' z int tp (aux n p)
aux n (Out' z int tp p)      = Out' z int tp (aux n p)
aux n (Evt' z int tp p)      = Evt' z int tp (aux n p)
aux n (Func' z cod tp p)     = Func' z cod tp (aux n p)
aux n (FuncI' z cod tp imp p)= FuncI' z cod tp (aux n imp) (aux n p)
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
