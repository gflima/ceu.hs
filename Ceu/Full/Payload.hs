module Ceu.Full.Payload where

import Ceu.Globals
import Ceu.Full.Grammar

-- remove:
-- (Int e True ...)  -> (Var e_ (Int e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitInt e v)     -> (Write e_ v) ; (EmitInt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
remove :: Stmt -> Stmt
remove (Var id Nothing p)        = Var id Nothing (remove p)
remove (Int int True p)          = Var ("_"++int) Nothing (Int int False (remove p))
remove (Int int False p)         = Int int False (remove p)
remove (AwaitExt ext (Just var)) = (AwaitExt ext Nothing) `Seq` (Write var (Read ("_"++ext)))
remove (AwaitInt int (Just var)) = (AwaitInt int Nothing) `Seq` (Write var (Read ("_"++int)))
remove (EmitInt  int (Just exp)) = (Write ("_"++int) exp) `Seq` (EmitInt int Nothing)
remove (If cnd p1 p2)            = If cnd (remove p1) (remove p2)
remove (Seq p1 p2)               = Seq (remove p1) (remove p2)
remove (Loop p)                  = Loop (remove p)
remove (Every evt (Just var) p)  = Every evt Nothing
                                     ((Write var (Read ("_"++evt))) `Seq` (remove p))
remove (Par' p1 p2)              = Par' (remove p1) (remove p2)
remove (Pause' var p)            = Pause' var (remove p)
remove (Fin' p)                  = Fin' (remove p)
remove (Trap' p)                 = Trap' (remove p)
remove (Clear' id p)             = Clear' id (remove p)
remove p                         = p
