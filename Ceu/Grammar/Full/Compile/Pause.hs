module Ceu.Grammar.Full.Compile.Pause where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..))
import Ceu.Grammar.Full.Stmt

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

aux (Data' z id vars cons abs p) = Data' z id vars cons abs (aux p)
aux (Var' z id tp Nothing p) = Var' z id tp Nothing (aux p)
aux (Inp' z id tp p)      = Inp' z id tp (aux p)
aux (Out' z id tp p)      = Out' z id tp (aux p)
aux (Evt' z id tp p)      = Evt' z id tp (aux p)
aux (Func' z id tp p)     = Func' z id tp (aux p)
aux (FuncI' z id tp imp p)= FuncI' z id tp (aux imp) (aux p)
aux (If z exp p1 p2)      = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)         = Seq z (aux p1) (aux p2)
aux (Loop z p)            = Loop z (aux p)
aux (Par z p1 p2)         = Par z (aux p1) (aux p2)
aux (And z p1 p2)         = And z (aux p1) (aux p2)
aux (Or z p1 p2)          = Or z (aux p1) (aux p2)
aux (Or' z p1 p2)         = Or' z (aux p1) (aux p2)
aux (Spawn z p)           = Spawn z (aux p)
aux (Trap' z p)           = Trap' z (aux p)
aux (Pause z evt p)       =
  Var' z ("__pause_var_"++evt) (Type1 "Int") Nothing
    (Evt' z ("__pause_int_"++evt) Type0
      (Seq z
        (Write z (LVar $ "__pause_var_"++evt) (Const z 0))
        (Or' z
          (Var' z "__tmp" (Type1 "Int") Nothing
            (Every z evt (Just $ LVar "__tmp")
              (If z (Call z "==" (Tuple z [(Read z "__tmp"),(Const z 0)]))
                  (Seq z (Write z (LVar $ "__pause_var_"++evt) (Const z 0))
                       (EmitEvt z ("__pause_int_"++evt) Nothing))
                  (Nop z))))
        (Or' z
          (Pause' z ("__pause_var_"++evt) p)
          (Var' z "__tmp" (Type1 "Int") Nothing
            (Every z evt (Just $ LVar "__tmp")
              (If z (Call z "==" (Tuple z [(Read z "__tmp"),(Const z 1)]))
                  (Write z (LVar $ "__pause_var_"++evt) (Const z 1))
                  (Nop z))))))))
aux p                     = p
