module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Stmt

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Data z id vars ors)       = Data z id vars ors
aux (Var z id tp fin)          = Var z id tp (aux_fin fin)
aux (FuncI z id tp p)          = FuncI z id tp (aux p)
aux (If z exp p1 p2)           = If z exp (aux p1) (aux p2)
aux (Seq z1 (Seq z2 p1 p2) p3) = aux $ Seq z1 p1 (Seq z2 p2 p3)
aux (Seq z p1 p2)              = Seq z (aux p1) (aux p2)
aux (Loop z p)                 = Loop z (aux p)
aux (Every z evt exp p)        = Every z evt exp (aux p)
aux (Par z p1 p2)              = Par z (aux p1) (aux p2)
aux (And z p1 p2)              = And z (aux p1) (aux p2)
aux (Or z p1 p2)               = Or z (aux p1) (aux p2)
aux (Spawn z p)                = Spawn z (aux p)
aux (Pause z evt p)            = Pause z evt (aux p)
aux (Fin z a b c)              = Fin z (aux a) (aux b) (aux c)
aux (Async z p)                = Async z (aux p)
aux (Trap z var p)             = Trap z var (aux p)
aux (Scope z p)                = Scope z (aux p)
aux p                          = p

aux_fin (Just (a,b,c)) = Just ((aux a),(aux b),(aux c))
aux_fin Nothing        = Nothing
