module Ceu.Full.Pause where

import Ceu.Globals
import Ceu.Full.Grammar

-- remove:
--  pause e do
--      <...>
--  end
--
--  var __e = 0;
--  pause __e do
--      par/or do
--          every __e in e do
--          end
--      with
--          <...>
--      end
--  end
remove :: Stmt -> Stmt
remove (Var id Nothing p)  = Var id Nothing (remove p)
remove (Int id b p)        = Int id b (remove p)
remove (If exp p1 p2)      = If exp (remove p1) (remove p2)
remove (Seq p1 p2)         = Seq (remove p1) (remove p2)
remove (Loop p)            = Loop (remove p)
remove (And p1 p2)         = And (remove p1) (remove p2)
remove (Or p1 p2)          = Or (remove p1) (remove p2)
remove (Spawn p)           = Spawn (remove p)
remove (Pause evt p)       =
  Var ("__pause_var_"++evt) Nothing
    (Int ("__pause_int_"++evt) False
      (Seq
        (Write ("__pause_var_"++evt) (Const 0))
        (Or
          (Var "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (Equ (Read "__tmp") (Const 0))
                  (Seq (Write ("__pause_var_"++evt) (Const 0))
                       (EmitInt ("__pause_int_"++evt) Nothing))
                  Nop)))
        (Or
          (Pause' ("__pause_var_"++evt) p)
          (Var "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (Equ (Read "__tmp") (Const 1))
                  (Write ("__pause_var_"++evt) (Const 1))
                  Nop)))))))
remove p                   = p
