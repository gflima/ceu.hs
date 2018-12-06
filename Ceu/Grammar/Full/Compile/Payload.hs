module Ceu.Grammar.Full.Compile.Payload where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Grammar

-- compile:
-- (Int' e True ...)  -> (Var' e_ (Int' e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitInt e v)     -> (Write e_ v) ; (EmitInt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
compile :: Stmt ann -> (Errors, Stmt ann)
compile p = ([], aux p)
aux (Var' z id Nothing p)       = Var' z id Nothing (aux p)
aux (Int' z int True p)         = Var' z ("_"++int) Nothing (Int' z int False (aux p))
aux (Int' z int False p)        = Int' z int False (aux p)
aux (AwaitExt z ext (Just var)) = Seq z (AwaitExt z ext Nothing) (Write z var (Read z ("_"++ext)))
aux (AwaitInt z int (Just var)) = Seq z (AwaitInt z int Nothing) (Write z var (Read z ("_"++int)))
aux (EmitInt z int (Just exp))  = Seq z (Write z ("_"++int) exp) (EmitInt z int Nothing)
aux (If z cnd p1 p2)            = If z cnd (aux p1) (aux p2)
aux (Seq z p1 p2)               = Seq z (aux p1) (aux p2)
aux (Loop z p)                  = Loop z (aux p)
aux (Every z evt (Just var) p)  = Every z evt Nothing
                                     (Seq z (Write z var (Read z ("_"++evt))) (aux p))
aux (Par' z p1 p2)              = Par' z (aux p1) (aux p2)
aux (Pause' z var p)            = Pause' z var (aux p)
aux (Fin' z p)                  = Fin' z (aux p)
aux (Trap' z p)                 = Trap' z (aux p)
aux (Clean' z id p)             = Clean' z id (aux p)
aux p                           = p
