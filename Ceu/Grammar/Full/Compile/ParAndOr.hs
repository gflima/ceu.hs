module Ceu.Grammar.Full.Compile.ParAndOr where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt ann -> (Errors, Stmt ann)
compile p = ([], aux p)

aux (Var' z var tp Nothing p) = Var' z var tp Nothing (aux p)
aux (Inp' z int b p)       = Inp' z int b (aux p)
aux (Out' z int b p)       = Out' z int b (aux p)
aux (Evt' z int b p)       = Evt' z int b (aux p)
aux (CodI' z cod inp out p) = CodI' z cod inp out (aux p)
aux (If z exp p1 p2)       = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)          = Seq z (aux p1) (aux p2)
aux (Loop z p)             = Loop z (aux p)
aux (Par z p1 p2)          = Par' z (aux p1) (aux p2)

aux (And z p1 p2)          = Clean' z "And"
                              (Trap' z
                                (Var' z "__and" (Type1 "Int") Nothing
                                  (Seq z
                                    (Write z "__and" (Const z 0))
                                    (Par' z p1' p2'))))
                             where
                              p1' = Seq z (Trap.ins' (aux p1)) check
                              p2' = Seq z (Trap.ins' (aux p2)) check
                              check = (If z (Call z "equ" (Tuple z [(Read z "__and"),(Const z 1)]))
                                        (Escape' z 0)
                                        (Seq z
                                          (Write z "__and" (Call z "add" (Tuple z [(Read z "__and"),(Const z 1)])))
                                          (Halt z)))

aux (Or z p1 p2)           = Clean' z "Or" (Trap' z (Par' z p1' p2')) where
                             p1' = (Seq z (Trap.ins' (aux p1)) (Escape' z 0))
                             p2' = (Seq z (Trap.ins' (aux p2)) (Escape' z 0))
aux (Or' z p1 p2)          = Clean' z "Or'" (Trap' z (Par' z p1' p2')) where
                             p1' = (Seq z (Trap.ins' (aux p1)) (Escape' z 0))
                             p2' = (Seq z (Trap.ins' (aux p2)) (Escape' z 0))
aux (Pause' z var p)       = Pause' z var (aux p)
aux (Trap' z p)            = Trap' z (aux p)
aux (Clean' z id p)        = Clean' z id (aux p)
aux p                      = p
