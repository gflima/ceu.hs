module Ceu.Eval where

import Ceu.Grammar
import Data.Maybe

-- Environment.
type Env = ([ID], [(ID,Val)])   -- declarations plus assignment history
type Envs = [Env]               -- list of environments

-- Stack level.
type Lvl = Int

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe Evt, Envs)

----------------------------------------------------------------------------
-- Environment

-- The empty environment.
newEnv :: Env
newEnv = ([], [])

-- Finds the first environment containing the given variable.
envsGet :: Envs -> String -> (Envs,Env,Envs)
envsGet [] _ = error "envsGet: bad environment"
envsGet envs id  = envsGet' [] envs id
  where
    envsGet' _ [] _       = error ("envsGet: undeclared variable: " ++ id)
    envsGet' notHere (env:maybeHere) id
      | elem id (fst env) = (notHere, env, maybeHere) -- found
      | otherwise         = envsGet' (notHere++[env]) maybeHere id

-- Writes value to variable in environment.
envsWrite :: Envs -> String -> Val -> Envs
envsWrite envs id val = envs1 ++ [(fst env, (id,val):(snd env))] ++ envs2
  where
    (envs1, env, envs2) = envsGet envs id

-- Reads variable value from environment.
envsRead :: Envs -> String -> Val
envsRead envs id = envsRead' hst id
  where
    (_, (_,hst), _) = envsGet envs id
    envsRead' [] id = error ("envsRead: uninitialized variable: " ++ id)
    envsRead' ((id',val'):hst') id
      | id == id' = val'    -- found
      | otherwise = envsRead' hst' id

-- Evaluates expression in environment.
envsEval :: Envs -> Expr -> Val
envsEval envs expr = case expr of
  Const val -> val
  Read id   -> envsRead envs id
  Umn e     -> negate $ envsEval envs e
  Add e1 e2 -> (envsEval envs e1) + (envsEval envs e2)
  Sub e1 e2 -> (envsEval envs e1) - (envsEval envs e2)

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
  Loop' p _  -> clear p
  And' p q   -> Seq (clear p) (clear q)
  Or' p q    -> Seq (clear p) (clear q)
  _          -> error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Desc
nst1Adv d f = (f p, n, e, envs)
  where
    (p, n, e, envs) = nst1 d

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Block vars p, n, Nothing, envs)           -- block
  = (Seq p (Restore (length envs)), n, Nothing, (vars,[]):envs)

nst1 (Restore lvl, n, Nothing, envs)            -- restore
  = (Nop, n, Nothing, drop (length envs - lvl) envs)

nst1 (Write id exp, n, Nothing, envs)           -- write
  = (Nop, n, Nothing, envsWrite envs id (envsEval envs exp))

nst1 (EmitInt e, n, Nothing, envs)              -- emit-int (pg 6)
  = (CanRun n, n, Just e, envs)

nst1 (CanRun m, n, Nothing, envs)               -- can-run (pg 6)
  | m == n    = (Nop, n, Nothing, envs)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq Nop q, n, Nothing, envs)              -- seq-nop (pg 6)
  = (q, n, Nothing, envs)

nst1 (Seq Break q, n, Nothing, envs)            -- seq-brk (pg 6)
  = (Break, n, Nothing, envs)

nst1 (Seq p q, n, Nothing, envs)                -- seq-adv (pg 6)
  = nst1Adv (p, n, Nothing, envs) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, envs)             -- if-true/false (pg 6)
  | envsEval envs exp /= 0 = (p, n, Nothing, envs)
  | otherwise              = (q, n, Nothing, envs)

nst1 (Loop p, n, Nothing, envs)                 -- loop-expd (pg 7)
  = (Seq (Loop' p p) (Restore (length envs)), n, Nothing, envs)

nst1 (Loop' Nop q, n, Nothing, envs)            -- loop-nop (pg 7)
  = (Loop q, n, Nothing, envs)

nst1 (Loop' Break q, n, Nothing, envs)          -- loop-brk (pg 7)
  = (Nop, n, Nothing, envs)

nst1 (Loop' p q, n, Nothing, envs)              -- loop-adv (pg 7)
  = nst1Adv (p, n, Nothing, envs) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, envs)                -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, Nothing, envs)

nst1 (And' Nop q, n, Nothing, envs)             -- and-nop1 (pg 7)
  = (q, n, Nothing, envs)

nst1 (And' Break q, n, Nothing, envs)           -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, envs)

nst1 (And' p Nop, n, Nothing, envs)             -- and-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Nop)
  | otherwise           = (p, n, Nothing, envs)

nst1 (And' p Break, n, Nothing, envs)           -- and-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, envs)

nst1 (And' p q, n, Nothing, envs)               -- and-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, envs) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, envs)                 -- or-expd (pg 7)
  = (Seq (Or' p (Seq (CanRun n) q)) (Restore (length envs)), n, Nothing, envs)

nst1 (Or' Nop q, n, Nothing, envs)              -- or-nop1 (pg 7)
  = (clear q, n, Nothing, envs)

nst1 (Or' Break q, n, Nothing, envs)            -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, envs)

nst1 (Or' p Nop, n, Nothing, envs)              -- or-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Nop)
  | otherwise           = (clear p, n, Nothing, envs)

nst1 (Or' p Break, n, Nothing, envs)            -- or-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, envs)

nst1 (Or' p q, n, Nothing, envs)                -- or-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, envs) (\q' -> Or' p q')

nst1 (Error msg, _, Nothing, _) = error ("Runtime error: " ++ msg)

nst1 (_, _, _, _) = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible desc = case desc of
  (Nop, n, e, envs)     -> True
  (Break, n, e, envs)   -> True
  (p, n, Just e, envs)  -> True
  (p, n, Nothing, envs) -> isBlocked n p

-- Zero or more nested transitions.
-- (pg 6)
nsts :: Desc -> Desc
nsts d
  | isNstIrreducible d = d
  | otherwise = nsts (nst1 d)

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
  _                     -> stmt -- nothing to do

-- (pg 6)
outPush :: Desc -> Desc
outPush (p, n, Just e, envs) = (bcast e p, n+1, Nothing, envs)
outPush (_, _, Nothing, _)   = error "outPush: missing event"

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, n, Nothing, envs)
  | n>0 && isNstIrreducible (p, n, Nothing, envs) = (p, n-1, Nothing, envs)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, n, Just e, envs)  = outPush (p, n, Just e, envs)
out1 (p, n, Nothing, envs) = outPop (p, n, Nothing, envs)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p, n, e, envs)
  | n == 0 = (p, n, e, envs)
  | n > 0  = nsts_out1_s $ out1 $ nsts (p, n, e, envs)

-- Counts the maximum number of EmitInt's that can be executed in a reaction
-- of program to event.
-- (pg 9)
pot :: Evt -> Stmt -> Int
pot e p = countMaxEmits $ bcast e p

-- (pg 9)
rank :: Desc -> (Int, Int)
rank (p, n, Nothing, envs) = (0, n)
rank (p, n, Just e, envs)  = (pot e p, n+1)

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && snd (rank d) == 0

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, Evt, Envs) -> (Stmt, Envs)
reaction (p, e, envs) = (p', envs')
  where
    (p', _, _, envs') = nsts_out1_s $ outPush (p, 0, Just e, envs)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: Stmt -> [Evt] -> Val
evalProg prog hist = evalProg' prog (inputBoot:hist) [(["ret"],[])]
  where                                      -- extra -1 for boot reaction
    evalProg' :: Stmt -> [Evt] -> Envs -> Val
    evalProg' prog hist envs = case prog of
      Nop | null hist -> envsRead envs "ret" -- done
          | otherwise -> error "evalProg: pending inputs"
      _   | null hist -> error "evalProg: program didn't terminate"
          | otherwise ->                     -- continue
            let (prog', envs') = reaction (prog, head hist, envs) in
              evalProg' prog' (tail hist) envs'
