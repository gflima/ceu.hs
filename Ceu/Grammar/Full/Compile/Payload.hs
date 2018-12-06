module Ceu.Grammar.Full.Compile.Payload where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Grammar

-- compile:
-- (Int' e True ...)  -> (Var' e_ (Int' e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitInt e v)     -> (Write e_ v) ; (EmitInt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux (Var' id Nothing p)       = Var' id Nothing (aux p)
aux (Int' int True p)         = Var' ("_"++int) Nothing (Int' int False (aux p))
aux (Int' int False p)        = Int' int False (aux p)
aux (AwaitExt ext (Just var)) = (AwaitExt ext Nothing) `Seq` (Write var (Read () ("_"++ext)))
aux (AwaitInt int (Just var)) = (AwaitInt int Nothing) `Seq` (Write var (Read () ("_"++int)))
aux (EmitInt  int (Just exp)) = (Write ("_"++int) exp) `Seq` (EmitInt int Nothing)
aux (If cnd p1 p2)            = If cnd (aux p1) (aux p2)
aux (Seq p1 p2)               = Seq (aux p1) (aux p2)
aux (Loop p)                  = Loop (aux p)
aux (Every evt (Just var) p)  = Every evt Nothing
                                     ((Write var (Read () ("_"++evt))) `Seq` (aux p))
aux (Par' p1 p2)              = Par' (aux p1) (aux p2)
aux (Pause' var p)            = Pause' var (aux p)
aux (Fin' p)                  = Fin' (aux p)
aux (Trap' p)                 = Trap' (aux p)
aux (Clean' id p)             = Clean' id (aux p)
aux p                         = p
