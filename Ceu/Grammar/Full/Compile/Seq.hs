module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Var var fin)            = Var var (aux_fin fin)
aux (If exp p1 p2)           = If exp (aux p1) (aux p2)
aux (Seq (Seq p1 p2) p3)     = aux $ Seq p1 (Seq p2 p3)
aux (Seq p1 p2)              = Seq (aux p1) (aux p2)
aux (Loop p)                 = Loop (aux p)
aux (Every evt exp p)        = Every evt exp (aux p)
aux (Par p1 p2)              = Par (aux p1) (aux p2)
aux (And p1 p2)              = And (aux p1) (aux p2)
aux (Or p1 p2)               = Or (aux p1) (aux p2)
aux (Spawn p)                = Spawn (aux p)
aux (Pause evt p)            = Pause evt (aux p)
aux (Fin a b c)              = Fin (aux a) (aux b) (aux c)
aux (Async p)                = Async (aux p)
aux (Trap var p)             = Trap var (aux p)
aux (Scope p)                = Scope (aux p)
aux p                        = p

aux_fin (Just (a,b,c)) = Just ((aux a),(aux b),(aux c))
aux_fin Nothing        = Nothing
