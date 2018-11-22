module Ceu.Full.Timer where

import Ceu.Globals
import qualified Ceu.Eval as E
import Ceu.Full.Grammar

-- remove:
--  var int tot_ = <DT>;
--  loop do
--      await TIMER;
--      tot_ = tot_ - 1;
--      if tot_ == 0 then
--          break;
--      end
--  end

remove :: Stmt -> Stmt
remove (Var id Nothing p) = Var id Nothing (remove p)
remove (Int id b p)       = Int id b (remove p)
remove (If exp p1 p2)     = If exp (remove p1) (remove p2)
remove (Seq p1 p2)        = Seq (remove p1) (remove p2)
remove (Loop p)           = Loop (remove p)
remove (Par' p1 p2)       = Par' (remove p1) (remove p2)
remove (Pause' var p)     = Pause' var (remove p)
remove (Trap' p)          = Trap' (remove p)
remove (Clean' id p)      = Clean' id (remove p)
remove (AwaitTmr exp)     = Var "__timer_await" Nothing
                                   (Seq
                                     (Write "__timer_await" exp)
                                     (Trap'
                                       (Loop (
                                         (AwaitExt "TIMER" Nothing)                `Seq`
                                         (Write "__timer_await"
                                           (Sub (Read "__timer_await") (Const 1))) `Seq`
                                         (If (Equ (Read "__timer_await") (Const 0))
                                           (Escape' 0))
                                           Nop
                                         ))))
remove p                  = p

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


