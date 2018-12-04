module Ceu.Grammar.Full.Compile.Pause where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Full.Grammar

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
compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)

aux (Var' id Nothing p) = Var' id Nothing (aux p)
aux (Int' id b p)       = Int' id b (aux p)
aux (If exp p1 p2)      = If exp (aux p1) (aux p2)
aux (Seq p1 p2)         = Seq (aux p1) (aux p2)
aux (Loop p)            = Loop (aux p)
aux (Par p1 p2)         = Par (aux p1) (aux p2)
aux (And p1 p2)         = And (aux p1) (aux p2)
aux (Or p1 p2)          = Or (aux p1) (aux p2)
aux (Or' p1 p2)         = Or' (aux p1) (aux p2)
aux (Spawn p)           = Spawn (aux p)
aux (Trap' p)           = Trap' (aux p)
aux (Pause evt p)       =
  Var' ("__pause_var_"++evt) Nothing
    (Int' ("__pause_int_"++evt) False
      (Seq
        (Write ("__pause_var_"++evt) (newExp$Const 0))
        (Or'
          (Var' "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (newExp$Equ (newExp$Read "__tmp") (newExp$Const 0))
                  (Seq (Write ("__pause_var_"++evt) (newExp$Const 0))
                       (EmitInt ("__pause_int_"++evt) Nothing))
                  Nop)))
        (Or'
          (Pause' ("__pause_var_"++evt) p)
          (Var' "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (newExp$Equ (newExp$Read "__tmp") (newExp$Const 1))
                  (Write ("__pause_var_"++evt) (newExp$Const 1))
                  Nop)))))))
aux p                   = p
