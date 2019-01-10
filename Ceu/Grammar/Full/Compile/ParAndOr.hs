module Ceu.Grammar.Full.Compile.ParAndOr where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..))
import Ceu.Grammar.Full.Stmt
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)

aux (Data' z tp vars ors p)   = Data' z tp vars ors (aux p)
aux (Var' z var tp Nothing p) = Var' z var tp Nothing (aux p)
aux (Inp' z int tp p)      = Inp' z int tp (aux p)
aux (Out' z int tp p)      = Out' z int tp (aux p)
aux (Evt' z int tp p)      = Evt' z int tp (aux p)
aux (Func' z cod tp p)     = Func' z cod tp (aux p)
aux (FuncI' z cod tp imp p)= FuncI' z cod tp (aux imp) (aux p)
aux (If z exp p1 p2)       = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)          = Seq z (aux p1) (aux p2)
aux (Loop z p)             = Loop z (aux p)
aux (Par z p1 p2)          = Par' z (aux p1) (aux p2)

aux (And z p1 p2)          = Clean' z "And"
                              (Trap' z
                                (Var' z "__and" (Type1 "Int") Nothing
                                  (Seq z
                                    (Write z (LVar "__and") (Const z 0))
                                    (Par' z p1' p2'))))
                             where
                              p1' = Seq z (Trap.ins' (aux p1)) check
                              p2' = Seq z (Trap.ins' (aux p2)) check
                              check = (If z (Call z "(==)" (Tuple z [(Read z "__and"),(Const z 1)]))
                                        (Escape' z 0)
                                        (Seq z
                                          (Write z (LVar "__and") (Call z "(+)" (Tuple z [(Read z "__and"),(Const z 1)])))
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
