module Ceu.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Data.Maybe
import Text.Printf
import Debug.Trace

-- Stack level.
type Lvl = Int

-- Environment.
type Vars = [(ID_Var, Maybe Val)]
type Evts = [(ID_Evt, Bool)]

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe ID_Evt, Vars)

-- Program (pg 5).
data Stmt
  = Evt ID_Evt Stmt             -- event declaration
  | Write ID_Var Expr           -- assignment statement
  | AwaitExt ID_Evt             -- await external event
  | AwaitInt ID_Evt             -- await internal event
  | EmitInt ID_Evt              -- emit internal event
  | Break                       -- loop escape
  | If Expr Stmt Stmt           -- conditional
  | Seq Stmt Stmt               -- sequence
  | Every ID_Evt Stmt           -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Fin Stmt                    -- finalization statement
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing purposes)
  | CanRun Int                  -- wait for stack level (internal)
  | Var' ID_Var (Maybe Val) Stmt -- block with environment store
  | Loop' Stmt Stmt             -- unrolled Loop (internal)
  | And' Stmt Stmt              -- unrolled And (internal)
  | Or' Stmt Stmt               -- unrolled Or (internal)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

fromGrammar :: G.Stmt -> Stmt
fromGrammar (G.Var id p)      = Var' id Nothing (fromGrammar p)
fromGrammar (G.Evt id p)      = Evt id (fromGrammar p)
fromGrammar (G.Write id exp)  = Write id exp
fromGrammar (G.AwaitExt id)   = AwaitExt id
fromGrammar (G.AwaitInt id)   = AwaitInt id
fromGrammar (G.EmitInt id)    = EmitInt id
fromGrammar G.Break           = Break
fromGrammar (G.If exp p1 p2)  = If exp (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq p1 p2)     = Seq (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Loop p)        = Loop' (fromGrammar p) (fromGrammar p)
fromGrammar (G.Every id p)    = Every id (fromGrammar p)
fromGrammar (G.And p1 p2)     = And (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Or p1 p2)      = Or (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Fin p)         = Fin (fromGrammar p)
fromGrammar G.Nop             = Nop
fromGrammar (G.Error msg)     = Error msg

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Evt id stmt    -> printf ":%s" id (sP stmt)
  Write var expr -> printf "%s=%s" var (sE expr)
  AwaitExt e     -> printf "?%s" e
  AwaitInt e     -> printf "?%s" e
  EmitInt e      -> printf "!%s" e
  Break          -> "break"
  If expr p q    -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq p q        -> printf "%s; %s" (sP p) (sP q)
  Every e p      -> printf "(every %s %s)" e (sP p)
  And p q        -> printf "(%s && %s)" (sP p) (sP q)
  Or p q         -> printf "(%s || %s)" (sP p) (sP q)
  Fin p          -> printf "(fin %s)" (sP p)
  Nop            -> "nop"
  Error _        -> "err"
  CanRun n       -> printf "@canrun(%d)" n
  Var' var val p
    | isNothing val -> printf "{%s=_: %s}" var (sP p)
    | otherwise     -> printf "{%s=%d: %s}" var (fromJust val) (sP p)
  Loop' p q      -> printf "(%s @loop %s)" (sP p) (sP q)
  And' p q       -> printf "(%s @&& %s)" (sP p) (sP q)
  Or' p q        -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExpr
    sP = showProg
    sV = showVars

----------------------------------------------------------------------------
-- Environment

-- Write value to variable in environment.
envWrite :: Vars -> ID_Var -> Val -> Vars
envWrite vars var val = case vars of
  (var',val'):vars'
    | var == var' -> (var,Just val):vars'
    | otherwise   -> (var',val'):(envWrite vars' var val)
  []              -> error ("envWrite: undeclared variable: " ++ var)

-- Reads variable value from environment.
envRead :: Vars -> ID_Var -> Val
envRead vars var = case vars of
  (var',val):vars'
    | var' == var -> if isJust val then fromJust val
                     else error ("envRead: uninitialized variable: " ++ var)
    | otherwise   -> envRead vars' var
  []              -> error ("envRead: undeclared variable: " ++ var)

-- Evaluates expression in environment.
envEval :: Vars -> Expr -> Val
envEval vars expr = case expr of
  Const val -> val
  Read var  -> envRead vars var
  Umn e     -> negate $ envEval vars e
  Add e1 e2 -> (envEval vars e1) + (envEval vars e2)
  Sub e1 e2 -> (envEval vars e1) - (envEval vars e2)
  Mul e1 e2 -> (envEval vars e1) * (envEval vars e2)
  Div e1 e2 -> (envEval vars e1) `div` (envEval vars e2)

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
  Evt _ p      -> isBlocked n p
  Var' _ _ p   -> isBlocked n p
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
  Evt _ p      -> clear p
  Var' _ _ p   -> clear p
  Loop' p _    -> clear p
  And' p q     -> Seq (clear p) (clear q)
  Or' p q      -> Seq (clear p) (clear q)
  _            -> error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Desc
nst1Adv d f = (f p, n, e, vars)
  where
    (p, n, e, vars) = nst1 d

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Var' var val Nop, n, Nothing, vars)     -- var-nop
  = (Nop, n, Nothing, vars)

nst1 (Var' var val Break, n, Nothing, vars)   -- var-brk
  = (Break, n, Nothing, vars)

nst1 (Var' var val p, n, Nothing, vars)       -- var-adv
  = (Var' var val' p', n, e, vars')
    where
      (p', _, e, (_,val'):vars') = nst1Adv (p, n, Nothing, (var,val):vars) id

nst1 (Evt id Nop, n, Nothing, vars)           -- evt-nop
  = (Nop, n, Nothing, vars)

nst1 (Evt id Break, n, Nothing, vars)         -- evt-brk
  = (Break, n, Nothing, vars)

nst1 (Evt id p, n, Nothing, vars)             -- evt-adv
  = (Evt id p', n, e, vars')
    where
      (p', _, e, vars') = nst1 (p, n, Nothing, vars)

nst1 (Write var expr, n, Nothing, vars)       -- write
  = (Nop, n, Nothing, envWrite vars var (envEval vars expr))

nst1 (EmitInt e, n, Nothing, vars)            -- emit-int (pg 6)
  = (CanRun n, n, Just e, vars)

nst1 (CanRun m, n, Nothing, vars)             -- can-run (pg 6)
  | m == n    = (Nop, n, Nothing, vars)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq Nop q, n, Nothing, vars)            -- seq-nop (pg 6)
  = (q, n, Nothing, vars)

nst1 (Seq Break q, n, Nothing, vars)          -- seq-brk (pg 6)
  = (Break, n, Nothing, vars)

nst1 (Seq p q, n, Nothing, vars)              -- seq-adv (pg 6)
  = nst1Adv (p, n, Nothing, vars) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, vars)           -- if-true/false (pg 6)
  | envEval vars exp /= 0 = (p, n, Nothing, vars)
  | otherwise              = (q, n, Nothing, vars)

nst1 (Loop' Nop q, n, Nothing, vars)          -- loop-nop (pg 7)
  = (Loop' q q, n, Nothing, vars)

nst1 (Loop' Break q, n, Nothing, vars)        -- loop-brk (pg 7)
  = (Nop, n, Nothing, vars)

nst1 (Loop' p q, n, Nothing, vars)            -- loop-adv (pg 7)
  = nst1Adv (p, n, Nothing, vars) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, vars)              -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, Nothing, vars)

nst1 (And' Nop q, n, Nothing, vars)           -- and-nop1 (pg 7)
  = (q, n, Nothing, vars)

nst1 (And' Break q, n, Nothing, vars)         -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, vars)

nst1 (And' p Nop, n, Nothing, vars)           -- and-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> And' p' Nop)
  | otherwise           = (p, n, Nothing, vars)

nst1 (And' p Break, n, Nothing, vars)         -- and-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> And' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, vars)

nst1 (And' p q, n, Nothing, vars)             -- and-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> And' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, vars) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, vars)               -- or-expd (pg 7)
  = (Or' p (Seq (CanRun n) q), n, Nothing, vars)

nst1 (Or' Nop q, n, Nothing, vars)            -- or-nop1 (pg 7)
  = (clear q, n, Nothing, vars)

nst1 (Or' Break q, n, Nothing, vars)          -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, vars)

nst1 (Or' p Nop, n, Nothing, vars)            -- or-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> Or' p' Nop)
  | otherwise           = (clear p, n, Nothing, vars)

nst1 (Or' p Break, n, Nothing, vars)          -- or-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> Or' p' Break)
  | otherwise           = (Seq (clear p) Break, n, Nothing, vars)

nst1 (Or' p q, n, Nothing, vars)              -- or-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, Nothing, vars) (\p' -> Or' p' q)
  | otherwise           = nst1Adv (q, n, Nothing, vars) (\q' -> Or' p q')

nst1 (Error msg, _, Nothing, _) = error ("Runtime error: " ++ msg)

nst1 (_, _, _, _) = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible desc = case desc of
  (Nop, n, e, vars)     -> True
  (Break, n, e, vars)   -> True
  (p, n, Just e, vars)  -> True
  (p, n, Nothing, vars) -> isBlocked n p

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
bcast :: ID_Evt -> Stmt -> Stmt
bcast e stmt = case stmt of
  AwaitExt e' | e == e' -> Nop
  AwaitInt e' | e == e' -> Nop
  Every e' p  | e == e' -> Seq p (Every e' p)
  Seq p q               -> Seq (bcast e p) q
  Evt id p              -> Evt id (bcast e p)
  Var' id val p         -> Var' id val (bcast e p)
  Loop' p q             -> Loop' (bcast e p) q
  And' p q              -> And' (bcast e p) (bcast e q)
  Or' p q               -> Or' (bcast e p) (bcast e q)
  _                     -> stmt -- nothing to do

-- (pg 6)
outPush :: Desc -> Desc
outPush (p, n, Just e, vars) = (bcast e p, n+1, Nothing, vars)
outPush (_, _, Nothing, _)   = error "outPush: missing event"

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, n, Nothing, vars)
  | n>0 && isNstIrreducible (p, n, Nothing, vars) = (p, n-1, Nothing, vars)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, n, Just e, vars)  = outPush (p, n, Just e, vars)
out1 (p, n, Nothing, vars) = outPop (p, n, Nothing, vars)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p, n, e, vars)
  | n == 0 = (p, n, e, vars)
  | n > 0  = nsts_out1_s $ out1 $ nsts (p, n, e, vars)

-- TODO: are these functions used anywhere?
{-
-- Counts the maximum number of EmitInt's that can be executed in program.
-- (pot', pg 9)
countMaxEmits :: Stmt -> Int
countMaxEmits stmt = case stmt of
  EmitInt e                      -> 1
  Var _ p                        -> cME p
  If expr p q                    -> max (cME p) (cME q)
  Loop p                         -> cME p
  And p q                        -> cME p + cME q
  Or p q                         -> cME p + cME q
  Seq Break q                    -> 0
  Seq (AwaitExt e) q             -> 0
  Seq p q                        -> cME p + cME q
  Var' _ _ p                     -> cME p
  Loop' p q | checkLoop (Loop p) -> cME p         -- q is unreachable
            | otherwise          -> cME p + cME q
  And' p q                       -> cME p + cME q -- CHECK THIS! --
  Or' p q                        -> cME p + cME q -- CHECK THIS! --
  _                              -> 0
  where
    cME = countMaxEmits

-- Counts the maximum number of EmitInt's that can be executed in a reaction
-- of program to event.
-- (pg 9)
pot :: ID_Evt -> Stmt -> Int
pot e p = countMaxEmits $ bcast e p

-- (pg 9)
rank :: Desc -> (Int, Int)
rank (p, n, Nothing, vars) = (0, n)
rank (p, n, Just e, vars)  = (pot e p, n+1)

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && snd (rank d) == 0
-}

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && iR d where
  iR (_,i,Nothing,_) = i == 0
  iR (_,_,Just ne,_) = True

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, ID_Evt, Vars) -> (Stmt, Vars)
reaction (p, e, vars) = (p', vars')
  where
    (p', _, _, vars') = nsts_out1_s $ outPush (p, 0, Just e, vars)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: G.Stmt -> [ID_Evt] -> Val
evalProg prog hist -- enclosing block with "ret" that never terminates
  = evalProg' (Var' "ret" Nothing (Seq (fromGrammar prog) (AwaitExt "FOREVER"))) ("BOOT":hist) []
  where
    evalProg' :: Stmt -> [ID_Evt] -> Vars -> Val
    evalProg' prog hist vars = case prog of
      (Var' "ret" val (AwaitExt "FOREVER"))
        | not (null hist) -> traceShow hist error "evalProg: pending inputs"
        | isNothing val   -> error "evalProg: no return"
        | otherwise       -> fromJust val
      _
        | null hist       -> traceShow prog error "evalProg: program didn't terminate"
        | otherwise       ->    -- continue
          let (prog', vars') = reaction (prog, head hist, vars) in
            evalProg' prog' (tail hist) vars'
