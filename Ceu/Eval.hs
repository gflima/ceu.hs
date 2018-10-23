module Ceu.Eval where

import Ceu.Grammar
import Data.Maybe
import Debug.Trace

-- Stack level.
type Lvl = Int

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe Evt)

----------------------------------------------------------------------------
-- Environment

envHas :: ID -> Env -> Bool
envHas id []                      = False
envHas id ((id',v):_) | (id==id') = True
envHas id (_:rest)                = envHas id rest

envRead :: ID -> Env -> Val
envRead id []                            = error ("envRead: undeclared variable: " ++ id)
envRead id ((id',Nothing):_) | (id==id') = error ("envRead: uninitialized variable: " ++ id)
envRead id ((id',Just v):_) | (id==id')  = v
envRead id (_:rest)                      = envRead id rest

-- Evaluates expression in environment.
envEval :: Expr -> Env -> Val
envEval expr env = case expr of
  Const val -> val
  Read id   -> envRead id env
  Umn e     -> negate $ envEval e env
  Add e1 e2 -> (envEval e1 env) + (envEval e2 env)
  Sub e1 e2 -> (envEval e1 env) - (envEval e2 env)
  Mul e1 e2 -> (envEval e1 env) * (envEval e2 env)
  Div e1 e2 -> (envEval e1 env) `div` (envEval e2 env)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked n stmt = case stmt of
  AwaitExt e -> True
  AwaitInt e -> True
  Every e p  -> True
  CanRun m   -> n > m
  Fin p      -> True
  Seq p q    -> isBlocked n p
  Local' _ p -> isBlocked n p
  Loop' p q  -> isBlocked n p
  And' p q   -> isBlocked n p && isBlocked n q
  Or' p q    -> isBlocked n p && isBlocked n q
  _          -> False

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  AwaitExt _ -> Nop
  AwaitInt _ -> Nop
  Every _ _  -> Nop
  CanRun _   -> Nop
  Fin p      -> p
  Seq p _    -> clear p
  Local' _ p -> clear p
  Loop' p _  -> clear p
  And' p q   -> Seq (clear p) (clear q)
  Or' p q    -> Seq (clear p) (clear q)
  _          -> error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Env -> Desc
nst1Adv d f env = (f p, n, e)
  where
    (p, n, e) = nst1 d env

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Env -> Desc

nst1 (Local vars p, n, Nothing) _           -- block
  = (Local' (map (\v->(v,Nothing)) vars) p, n, Nothing)

nst1 (Local' _ Nop, n, Nothing) _           -- block'-nop
  = (Nop, n, Nothing)

nst1 (Local' env' p, n, Nothing) env =
  let p1 = (Local' env' p)
      p2 = f1 p1 env
  in
    if p1 /= p2 then    -- block'-write
      (p2, n, Nothing)
    else                -- block'-adv
      nst1Adv (p, n, Nothing) (\p' -> Local' env' p') (env'++env)
  where
    f1 :: Stmt -> Env -> Stmt
    f1 p env =
      let ret = (f2 p env) in
        case ret of
          (p', Nothing)    -> p'
          (_, Just (id,_)) -> error ("Write: undeclared variable: " ++ id)

    f2 :: Stmt -> Env -> (Stmt, Maybe (ID,Val))
    f2 (Write id exp) env = (Nop, Just (id, envEval exp env))
    f2 (Seq p1 p2)    env = (Seq   p1' p2,  v) where (p1',v) = (f2 p1 env)
    f2 (Every e p)    env = (Every e   p',  v) where (p', v) = (f2 p env)
    f2 (Loop' p1 p2)  env = (Loop' p1' p2,  v) where (p1',v) = (f2 p1 env)
    f2 (And'  p1 p2)  env = (And'  p1' p2', v) where
      (p1',v1) = (f2 p1 env)
      (p2',v2) = (f2 p2 env)
      v = case v1 of
        Nothing   -> v2
        otherwise -> v1
    f2 (Or'  p1 p2) env   = (Or' p1' p2', v) where
      (p1',v1) = (f2 p1 env)
      (p2',v2) = (f2 p2 env)
      v = case v1 of
        Nothing   -> v2
        otherwise -> v1

    f2 (Local' env' p) env =
      case (f2 p (env'++env)) of
        (p', Nothing)       -> (Local' env' p', Nothing)
        (p', Just (id,val)) ->
          if (envHas id env') then
            (Local' ((id, Just val):env') p', Nothing)
          else
            (Local' env' p', Just (id,val))

    f2 p _ = (p, Nothing)

nst1 (EmitInt e, n, Nothing) _                  -- emit-int (pg 6)
  = (CanRun n, n, Just e)

nst1 (CanRun m, n, Nothing) _                   -- can-run (pg 6)
  | m == n    = (Nop, n, Nothing)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq Nop q, n, Nothing) _                  -- seq-nop (pg 6)
  = (q, n, Nothing)

nst1 (Seq Break q, n, Nothing) _                -- seq-brk (pg 6)
  = (Break, n, Nothing)

nst1 (Seq p q, n, Nothing) env                  -- seq-adv (pg 6)
  = nst1Adv (p, n, Nothing) (\p' -> Seq p' q) env

nst1 (If exp p q, n, Nothing) env               -- if-true/false (pg 6)
  | envEval exp env /= 0 = (p, n, Nothing)
  | otherwise            = (q, n, Nothing)

nst1 (Loop p, n, Nothing) _                     -- loop-expd (pg 7)
  = ((Loop' p p), n, Nothing)

nst1 (Loop' Nop q, n, Nothing) _                -- loop-nop (pg 7)
  = (Loop q, n, Nothing)

nst1 (Loop' Break q, n, Nothing) _              -- loop-brk (pg 7)
  = (Nop, n, Nothing)

nst1 (Loop' p q, n, Nothing) env                -- loop-adv (pg 7)
  = nst1Adv (p, n, Nothing) (\p' -> Loop' p' q) env

nst1 (And p q, n, Nothing) _                    -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, Nothing)

nst1 (And' Nop q, n, Nothing) _                 -- and-nop1 (pg 7)
  = (q, n, Nothing)

nst1 (And' Break q, n, Nothing) _               -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing)

nst1 (And' p Nop, n, Nothing) env               -- and-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> And' p' Nop) env
  | otherwise           = (p, n, Nothing)

nst1 (And' p Break, n, Nothing) env             -- and-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> And' p' Break) env
  | otherwise           = (Seq (clear p) Break, n, Nothing)

nst1 (And' p q, n, Nothing) env                 -- and-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> And' p' q) env
  | otherwise           = nst1Adv (q, n, Nothing) (\q' -> And' p q') env

nst1 (Or p q, n, Nothing) _                     -- or-expd (pg 7)
  = (Or' p (Seq (CanRun n) q), n, Nothing)

nst1 (Or' Nop q, n, Nothing) _                  -- or-nop1 (pg 7)
  = (clear q, n, Nothing)

nst1 (Or' Break q, n, Nothing) _                -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing)

nst1 (Or' p Nop, n, Nothing) env                -- or-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> Or' p' Nop) env
  | otherwise           = (clear p, n, Nothing)

nst1 (Or' p Break, n, Nothing) env              -- or-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> Or' p' Break) env
  | otherwise           = (Seq (clear p) Break, n, Nothing)

nst1 (Or' p q, n, Nothing) env                  -- or-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing) (\p' -> Or' p' q) env
  | otherwise           = nst1Adv (q, n, Nothing) (\q' -> Or' p q') env

nst1 (Error msg, _, Nothing) _ = error ("Runtime error: " ++ msg)

nst1 d _ = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible desc = case desc of
  (Nop, n, e)     -> True
  (Break, n, e)   -> True
  (p, n, Just e)  -> True
  (p, n, Nothing) -> isBlocked n p

-- Zero or more nested transitions.
-- (pg 6)
nsts :: Desc -> Desc
nsts d
  | isNstIrreducible d = d
  | otherwise = nsts (nst1 d [])

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
  Loop' p q             -> Loop' (bcast e p) q
  And' p q              -> And' (bcast e p) (bcast e q)
  Or' p q               -> Or' (bcast e p) (bcast e q)
  Local' env p          -> Local' env (bcast e p)
  _                     -> stmt -- nothing to do

-- (pg 6)
outPush :: Desc -> Desc
outPush (p, n, Just e)  = (bcast e p, n+1, Nothing)
outPush (_, _, Nothing) = error "outPush: missing event"

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, n, Nothing)
  | n>0 && isNstIrreducible (p, n, Nothing) = (p, n-1, Nothing)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, n, Just e)  = outPush (p, n, Just e)
out1 (p, n, Nothing) = outPop (p, n, Nothing)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p, n, e)
  | n == 0 = (p, n, e)
  | n > 0  = nsts_out1_s $ out1 $ nsts (p, n, e)

-- Counts the maximum number of EmitInt's that can be executed in a reaction
-- of program to event.
-- (pg 9)
pot :: Evt -> Stmt -> Int
pot e p = countMaxEmits $ bcast e p

-- (pg 9)
rank :: Desc -> (Int, Int)
rank (p, n, Nothing) = (0, n)
rank (p, n, Just e)  = (pot e p, n+1)

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && snd (rank d) == 0

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, Evt) -> Stmt
reaction (p, e) = p'
  where
    (p', _, _) = nsts_out1_s $ outPush (p, 0, Just e)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: Stmt -> [Evt] -> Val
evalProg prog hist = evalProg' (Local ["ret"] (Seq prog (AwaitExt inputForever))) (inputBoot:hist)
  where                         -- enclosing block with "ret" that never terminates
    evalProg' :: Stmt -> [Evt] -> Val
    evalProg' prog hist = case prog of
      (Local' env (AwaitExt inputForever))
          | null hist -> envRead "ret" env  -- done
          | otherwise -> error "evalProg: pending inputs"
      p   | null hist -> (trace (show p) error "evalProg: program didn't terminate")
          | otherwise ->                     -- continue
            let prog' = reaction (prog, head hist) in
              evalProg' prog' (tail hist)
