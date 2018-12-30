module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux :: Stmt -> Stmt
aux (Var z var tp fin)              = Var' z var tp (aux_fin fin) (Nop z)
aux (Inp z inp b)                   = Inp' z inp b (Nop z)
aux (Out z out b)                   = Out' z out b (Nop z)
aux (Evt z int b)                   = Evt' z int b (Nop z)
aux (Func z cod tp)                 = Func' z cod tp (Nop z)
aux (FuncI z cod tp imp)            = FuncI' z cod tp imp (Nop z)
aux (If z exp p1 p2)                = If z exp (aux p1) (aux p2)
aux (Seq _ s@(Inp z inp b) p2)      = Inp' z inp b (aux p2)
aux (Seq _ s@(Out z out b) p2)      = Out' z out b (aux p2)
aux (Seq _ s@(Var z var tp fin) p2) = Var' z var tp (aux_fin fin) (aux p2)
aux (Seq _ s@(Evt z int b) p2)      = Evt' z int b (aux p2)
aux (Seq _ s@(Func z cod tp) p2)    = Func' z cod tp (aux p2)
aux (Seq _ s@(FuncI z cod tp imp) p2) = FuncI' z cod tp (fmap aux imp) (aux p2)
aux (Seq z p1 p2)                   = Seq z (aux p1) (aux p2)
aux (Loop z p)                      = Loop z (aux p)
aux (Every z evt exp p)             = Every z evt exp (aux p)
aux (Par z p1 p2)                   = Par z (aux p1) (aux p2)
aux (And z p1 p2)                   = And z (aux p1) (aux p2)
aux (Or z p1 p2)                    = Or z (aux p1) (aux p2)
aux (Spawn z p)                     = Spawn z (aux p)
aux (Pause z evt p)                 = Pause z evt (aux p)
aux (Fin z a b c)                   = Fin z (aux a) (aux b) (aux c)
aux (Async z p)                     = Async z (aux p)
aux (Trap z var p)                  = Trap z var (aux p)
aux (Scope _ p)                     = (aux p)
aux p                               = p

aux_fin (Just (a,b,c)) = Just ((aux a),(aux b),(aux c))
aux_fin Nothing        = Nothing
