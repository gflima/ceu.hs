module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Var var (Just val) fin) = Seq (Var' var (aux_fin fin) Nop) (Write var val)
aux (Var var Nothing fin)    = Var' var (aux_fin fin) Nop
aux (Int int b)              = Int' int b Nop
aux (If exp p1 p2)           = If exp (aux p1) (aux p2)
aux (Seq s@(Var var (Just val) fin) p2) = Var' var (aux_fin fin) (Seq (Write var val) (aux p2))
aux (Seq s@(Var var Nothing fin) p2)    = Var' var (aux_fin fin) (aux p2)
aux (Seq s@(Int int b) p2)   = Int' int b (aux p2)
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
aux (Scope p)                = (aux p)
aux p                        = p

aux_fin (Just (a,b,c)) = Just ((aux a),(aux b),(aux c))
aux_fin Nothing        = Nothing
