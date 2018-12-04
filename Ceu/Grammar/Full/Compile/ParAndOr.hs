module Ceu.Grammar.Full.Compile.ParAndOr where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Trap as Trap

-- compile

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)

aux (Var' var Nothing p) = Var' var Nothing (aux p)
aux (Int' int b p)       = Int' int b (aux p)
aux (If exp p1 p2)       = If exp (aux p1) (aux p2)
aux (Seq p1 p2)          = Seq (aux p1) (aux p2)
aux (Loop p)             = Loop (aux p)
aux (Par p1 p2)          = Par' (aux p1) (aux p2)

aux (And p1 p2)          = Trap' (Var' "__and" Nothing
                            (Seq
                              (Write "__and" (Exp$Const 0))
                              (Par' p1' p2')))
                          where
                            p1' = Seq (Trap.ins' (aux p1)) check
                            p2' = Seq (Trap.ins' (aux p2)) check
                            check = (If (Exp$Equ (Exp$Read "__and") (Exp$Const 1))
                                      (Escape' 0)
                                      (Seq
                                        (Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1)))
                                        AwaitFor))

aux (Or p1 p2)           = Clean' "Or" (Trap' (Par' p1' p2')) where
                            p1' = (Seq (Trap.ins' (aux p1)) (Escape' 0))
                            p2' = (Seq (Trap.ins' (aux p2)) (Escape' 0))
aux (Or' p1 p2)          = Clean' "Or'" (Trap' (Par' p1' p2')) where
                            p1' = (Seq (Trap.ins' (aux p1)) (Escape' 0))
                            p2' = (Seq (Trap.ins' (aux p2)) (Escape' 0))
aux (Pause' var p)       = Pause' var (aux p)
aux (Trap' p)            = Trap' (aux p)
aux (Clean' id p)        = Clean' id (aux p)
aux p                    = p
