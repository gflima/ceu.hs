module Ceu.Grammar.Full.Compile.Break where

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux (-1) p)

aux :: Int -> Stmt -> Stmt
aux n (Var' var Nothing p) = Var' var Nothing (aux n p)
aux n (Int' int b p)       = Int' int b (aux n p)
aux n (If exp p1 p2)       = If exp (aux n p1) (aux n p2)
aux n (Seq p1 p2)          = Seq (aux n p1) (aux n p2)
aux n (Loop p)             = Clean' "Loop" (Trap' (Loop (aux (n+1) (Trap.ins' p))))
--aux (-1) Break            = error "remBreak: `break` without `loop`"
aux n Break                = Escape' n
aux n (Every evt var p)    = Every evt var (aux n p)
aux n (Par' p1 p2)         = Par' (aux n p1) (aux n p2)
aux n (Pause' var p)       = Pause' var (aux n p)
aux n (Fin' p)             = Fin' (aux n p)
aux n (Trap' p)            = Trap' (aux (n+1) p)
aux n (Clean' id p)        = Clean' id (aux n p)
aux n p                    = p
