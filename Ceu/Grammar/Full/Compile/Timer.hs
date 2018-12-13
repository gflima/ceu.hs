module Ceu.Grammar.Full.Compile.Timer where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import qualified Ceu.Eval as E
import Ceu.Grammar.Full.Grammar

-- compile:
--  var int tot_ = <DT>;
--  loop do
--      await TIMER;
--      tot_ = tot_ - 1;
--      if tot_ == 0 then
--          break;
--      end
--  end

compile :: Stmt ann -> (Errors, Stmt ann)
compile p = ([], aux p)
aux (Var' z id Nothing p) = Var' z id Nothing (aux p)
aux (Evt' z id b p)       = Evt' z id b (aux p)
aux (Out' z id b p)       = Out' z id b (aux p)
aux (If z exp p1 p2)      = If z exp (aux p1) (aux p2)
aux (Seq z p1 p2)         = Seq z (aux p1) (aux p2)
aux (Loop z p)            = Loop z (aux p)
aux (Par' z p1 p2)        = Par' z (aux p1) (aux p2)
aux (Pause' z var p)      = Pause' z var (aux p)
aux (Trap' z p)           = Trap' z (aux p)
aux (Clean' z id p)       = Clean' z id (aux p)
aux (AwaitTmr z exp)      = Var' z "__timer_await" Nothing
                            (Seq z
                              (Write z "__timer_await" exp)
                              (Trap' z
                                (Loop z
                                  (Seq z
                                    (AwaitInp z "TIMER" Nothing)
                                    (Seq z
                                      (Write z "__timer_await"
                                        (Sub z (Read z "__timer_await") (Const z 1)))
                                      (If z (Equ z (Read z "__timer_await") (Const z 0))
                                        (Escape' z 0)
                                        (Nop z)))))))
aux p                     = p

-- expand:
-- expands ("TIMER",v) -> ("TIMER",Nothing) * v
expand :: [In] -> [In]
expand []                      = []
expand (("TIMER", Just 0):ins) = (expand ins)
expand (("TIMER", Just v):ins) = ("TIMER",Nothing) : (expand $ ("TIMER",Just(v-1)) : ins)
expand (x:ins)                 = x : (expand ins)

-- join:
-- joins --N outs w/ X out-- from TIMER into --1 outs w/ N*X out--
-- Boot, Timer,2
-- [a]   [b] [c] -> [ [a], [b], [c] ] => [ [a],[b,c] ]
join :: [In] -> [E.Outs] -> [E.Outs]
join [] []                                       = []
join (("TIMER", Just 1):ins) (outs:outss)        = outs : (join ins outss)
join (("TIMER", Just v):ins) (outs1:outs2:outss) = join (("TIMER",Just(v-1)):ins) ((outs1++outs2):outss)
join (x:ins) (outs:outss)                        = outs : (join ins outss)


