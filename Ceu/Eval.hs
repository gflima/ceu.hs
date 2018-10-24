module Ceu.Eval where

import Ceu.Grammar
import Data.Maybe
import Debug.Trace

-- Environment.
type Env = [(Var,Maybe Val)]

-- Stack level.
type Lvl = Int

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe Evt, Env)

----------------------------------------------------------------------------
-- Environment

-- Write value to variable in environment.
envWrite :: Env -> Var -> Val -> Env
envWrite env var val = case env of
  (var',val'):env'
    | var == var' -> (var,Just val):env'
    | otherwise   -> (var',val'):(envWrite env' var val)
  []              -> error ("envWrite: undeclared variable: " ++ var)

-- Reads variable value from environment.
envRead :: Env -> Var -> Val
envRead env var = case env of
  (var',val):env'
    | var' == var -> if isJust val then fromJust val
                     else error ("envRead: uninitialized variable: " ++ var)
    | otherwise   -> envRead env' var
  []              -> error ("envRead: undeclared variable: " ++ var)

-- Evaluates expression in environment.
envEval :: Env -> Expr -> Val
envEval env expr = case expr of
  Const val -> val
  Read var  -> envRead env var
  Umn e     -> negate $ envEval env e
  Add e1 e2 -> (envEval env e1) + (envEval env e2)
  Sub e1 e2 -> (envEval env e1) - (envEval env e2)
  Mul e1 e2 -> (envEval env e1) * (envEval env e2)
  Div e1 e2 -> (envEval env e1) `div` (envEval env e2)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked n stmt = case stmt of
  AwaitExt e   -> True
  AwaitInt e   -> True
  Every e p    -> True
  CanRun m     -> n > m
  Fin p        -> True
  Seq p q      -> isBlocked n p
  Local' _ _ p -> isBlocked n p
  Loop' p q    -> isBlocked n p
  And' p q     -> isBlocked n p && isBlocked n q
  Or' p q      -> isBlocked n p && isBlocked n q
  _            -> False

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  AwaitExt _   -> Nop
  AwaitInt _   -> Nop
  Every _ _    -> Nop
  CanRun _     -> Nop
  Fin p        -> p
  Seq p _      -> clear p
  Local' _ _ p -> clear p
  Loop' p _    -> clear p
  And' p q     -> Seq (clear p) (clear q)
  Or' p q      -> Seq (clear p) (clear q)
  _            -> error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Desc
nst1Adv d f = (f p, n, e, env)
  where
    (p, n, e, env) = nst1 d

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Local var p, n, Nothing, env)            -- local-exp
  = (Local' var Nothing p, n, Nothing, env)

nst1 (Local' var val Nop, n, Nothing, env)     -- local-nop
  = (Nop, n, Nothing, env)

nst1 (Local' var val Break, n, Nothing, env)   -- local-brk
  = (Break, n, Nothing, env)

nst1 (Local' var val p, n, Nothing, env)       -- local-adv
  = (Local' var val' p', n, e, env')
    where
      (p', _, e, (_,val'):env') = nst1Adv (p, n, Nothing, (var,val):env) id

nst1 (Write var expr, n, Nothing, env)         -- write
  = (Nop, n, Nothing, envWrite env var (envEval env expr))

nst1 (EmitInt e, n, Nothing, env)              -- emit-int (pg 6)
  = (CanRun n, n, Just e, env)

nst1 (CanRun m, n, Nothing, env)               -- can-run (pg 6)
  | m == n    = (Nop, n, Nothing, env)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq Nop q, n, Nothing, env)              -- seq-nop (pg 6)
  = (q, n, Nothing, env)

nst1 (Seq Break q, n, Nothing, env)            -- seq-brk (pg 6)
  = (Break, n, Nothing, env)

nst1 (Seq p q, n, Nothing, env)                -- seq-adv (pg 6)
  = nst1Adv (p, n, Nothing, env) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, env)             -- if-true/false (pg 6)
  | envEval env exp /= 0 = (p, n, Nothing, env)
  | otherwise              = (q, n, Nothing, env)

nst1 (Loop p, n, Nothing, env)                 -- loop-expd (pg 7)
  = ((Loop' p p), n, Nothing, env)

nst1 (Loop' Nop q, n, Nothing, env)            -- loop-nop (pg 7)
  = (Loop q, n, Nothing, env)

nst1 (Loop' Break q, n, Nothing, env)          -- loop-brk (pg 7)
  = (Nop, n, Nothing, env)

nst1 (Loop' p q, n, Nothing, env)              -- loop-adv (pg 7)
  = nst1Adv (p, n, Nothing, env) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, env)                -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, Nothing, env)

nst1 (And' Nop q, n, Nothing, env)             -- and-nop1 (pg 7)
  = (q, n, Nothing, env)

nst1 (And' Break q, n, Nothing, env)           -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, env)

nst1 (And' p Nop, n, Nothing, env)             -- and-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> And' p' Nop)
  | otherwise           = (p, n, Nothing, env)

nst1 (And' p Break, n, Nothing, env)           -- and-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> And' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, env)

nst1 (And' p q, n, Nothing, env)               -- and-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> And' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, env) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, env)                 -- or-expd (pg 7)
  = (Or' p (Seq (CanRun n) q), n, Nothing, env)

nst1 (Or' Nop q, n, Nothing, env)              -- or-nop1 (pg 7)
  = (clear q, n, Nothing, env)

nst1 (Or' Break q, n, Nothing, env)            -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, env)

nst1 (Or' p Nop, n, Nothing, env)              -- or-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' Nop)
  | otherwise           = (clear p, n, Nothing, env)

nst1 (Or' p Break, n, Nothing, env)            -- or-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, env)

nst1 (Or' p q, n, Nothing, env)                -- or-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, env) (\q' -> Or' p q')

nst1 (Error msg, _, Nothing, _) = error ("Runtime error: " ++ msg)

nst1 (_, _, _, _) = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible desc = case desc of
  (Nop, n, e, env)     -> True
  (Break, n, e, env)   -> True
  (p, n, Just e, env)  -> True
  (p, n, Nothing, env) -> isBlocked n p

-- Zero or more nested transitions.
-- (pg 6)
nsts :: Desc -> Desc
nsts d
  | isNstIrreducible d = d
--  | otherwise = traceShow d (nsts (nst1 d))
  | otherwise = nsts $ nst1 d

----------------------------------------------------------------------------
-- Outermost transition

-- Awakes all trails waiting for the given event.
-- (pg 8, fig 4.i)
bcast :: Evt -> Stmt -> Stmt
bcast e stmt = case stmt of
  AwaitExt e' | e == e' -> Nop
  AwaitInt e' | e == e' -> Nop
  Every e' p  | e == e' -> Seq p (Every e' p)
  Seq p q               -> Seq (bcast e p) q
  Local' var val p      -> Local' var val (bcast e p)
  Loop' p q             -> Loop' (bcast e p) q
  And' p q              -> And' (bcast e p) (bcast e q)
  Or' p q               -> Or' (bcast e p) (bcast e q)
  _                     -> stmt -- nothing to do

-- (pg 6)
outPush :: Desc -> Desc
outPush (p, n, Just e, env) = (bcast e p, n+1, Nothing, env)
outPush (_, _, Nothing, _)   = error "outPush: missing event"

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, n, Nothing, env)
  | n>0 && isNstIrreducible (p, n, Nothing, env) = (p, n-1, Nothing, env)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, n, Just e, env)  = outPush (p, n, Just e, env)
out1 (p, n, Nothing, env) = outPop (p, n, Nothing, env)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p, n, e, env)
  | n == 0 = (p, n, e, env)
  | n > 0  = nsts_out1_s $ out1 $ nsts (p, n, e, env)

-- Counts the maximum number of EmitInt's that can be executed in a reaction
-- of program to event.
-- (pg 9)
pot :: Evt -> Stmt -> Int
pot e p = countMaxEmits $ bcast e p

-- (pg 9)
rank :: Desc -> (Int, Int)
rank (p, n, Nothing, env) = (0, n)
rank (p, n, Just e, env)  = (pot e p, n+1)

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && snd (rank d) == 0

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, Evt, Env) -> (Stmt, Env)
reaction (p, e, env) = (p', env')
  where
    (p', _, _, env') = nsts_out1_s $ outPush (p, 0, Just e, env)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: Stmt -> [Evt] -> Val
evalProg prog hist -- enclosing block with "ret" that never terminates
  = evalProg' (Local "ret" (Seq prog (AwaitExt inputForever))) (inputBoot:hist) []
  where
    evalProg' :: Stmt -> [Evt] -> Env -> Val
    evalProg' prog hist env = case prog of
      (Local' "ret" val (AwaitExt inputForever))
        | not (null hist) -> traceShow hist error "evalProg: pending inputs"
        | isNothing val   -> error "evalProg: no return"
        | otherwise       -> fromJust val
      _
        | null hist       -> traceShow prog error "evalProg: program didn't terminate"
        | otherwise       ->    -- continue
          let (prog', env') = reaction (prog, head hist, env) in
            evalProg' prog' (tail hist) env'
