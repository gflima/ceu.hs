module Ceu.Grammar.Full.Compile.Payload where

import Data.Char (toUpper)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..))
import Ceu.Grammar.Full.Grammar

-- compile:
-- (Evt' e True ...)  -> (Var' e_ (Evt' e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitEvt e v)     -> (Write e_ v) ; (EmitEvt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux (Var' z id tp Nothing p)    = Var' z id tp Nothing (aux p)
aux (Inp' z id b p)             = Inp' z id b (aux p)
aux (Out' z id b p)             = Out' z id b (aux p)
aux (Evt' z int True p)         = Var' z ("_"++int) (Type1 "Int") Nothing (Evt' z int False (aux p))
aux (Evt' z int False p)        = Evt' z int False (aux p)
aux (Func' z id tp p)           = Func' z id tp (aux p)
aux (FuncI' z id tp imp p)      = FuncI' z id tp (fmap aux imp) (aux p)
aux (AwaitInp z ext (Just var)) = Seq z (AwaitInp z ext Nothing) (Write z var (Read z "_INPUT"))
aux (AwaitEvt z int (Just var)) = Seq z (AwaitEvt z int Nothing) (Write z var (Read z ("_"++int)))
aux (EmitEvt z int (Just exp))  = Seq z (Write z ("_"++int) exp) (EmitEvt z int Nothing)
aux (If z cnd p1 p2)            = If z cnd (aux p1) (aux p2)
aux (Seq z p1 p2)               = Seq z (aux p1) (aux p2)
aux (Loop z p)                  = Loop z (aux p)
aux (Every z evt (Just var) p)  = Every z evt Nothing
                                     (Seq z (Write z var (Read z inp)) (aux p))
                                  where
                                    inp = if (map toUpper evt) == evt then "_INPUT" else "_"++evt
aux (Par' z p1 p2)              = Par' z (aux p1) (aux p2)
aux (Pause' z var p)            = Pause' z var (aux p)
aux (Fin' z p)                  = Fin' z (aux p)
aux (Trap' z p)                 = Trap' z (aux p)
aux (Clean' z id p)             = Clean' z id (aux p)
aux p                           = p
