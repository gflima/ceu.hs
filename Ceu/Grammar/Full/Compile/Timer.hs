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

compile :: Stmt -> (Errors, Stmt)
compile p = ([], aux p)
aux (Var' id Nothing p) = Var' id Nothing (aux p)
aux (Int' id b p)       = Int' id b (aux p)
aux (If exp p1 p2)      = If exp (aux p1) (aux p2)
aux (Seq p1 p2)         = Seq (aux p1) (aux p2)
aux (Loop p)            = Loop (aux p)
aux (Par' p1 p2)        = Par' (aux p1) (aux p2)
aux (Pause' var p)      = Pause' var (aux p)
aux (Trap' p)           = Trap' (aux p)
aux (Clean' id p)       = Clean' id (aux p)
aux (AwaitTmr exp)      = Var' "__timer_await" Nothing
                           (Seq
                             (Write "__timer_await" exp)
                             (Trap'
                               (Loop (
                                 (AwaitExt "TIMER" Nothing)                `Seq`
                                 (Write "__timer_await"
                                   (Sub () (Read () "__timer_await") (Const () 1))) `Seq`
                                 (If (Equ () (Read () "__timer_await") (Const () 0))
                                   (Escape' 0))
                                   Nop
                                 ))))
aux p                   = p

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


