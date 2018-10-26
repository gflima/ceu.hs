module Ceu.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Data.Maybe
import Text.Printf
import Debug.Trace

type Lvl = Int

-- Environment.
type Vars = [(ID_Var, Maybe Val)]
type Evts = [(ID_Evt, Bool)]

-- Description (pg 6).
type Desc = (Stmt, Lvl, Vars, Evts)

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
  | CanRun Lvl                  -- wait for stack level (internal)
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
  Evt id stmt    -> printf ":%s %s" id (sP stmt)
  Write var expr -> printf "%s=%s" var (sE expr)
  AwaitExt evt     -> printf "?%s" evt
  AwaitInt evt     -> printf "?%s" evt
  EmitInt evt      -> printf "!%s" evt
  Break          -> "break"
  If expr p q    -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq p q        -> printf "%s; %s" (sP p) (sP q)
  Every evt p      -> printf "(every %s %s)" evt (sP p)
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
varsWrite :: Vars -> ID_Var -> Val -> Vars
varsWrite vars var val = case vars of
  (var',val'):vars'
    | var == var' -> (var,Just val):vars'
    | otherwise   -> (var',val'):(varsWrite vars' var val)
  []              -> error ("varsWrite: undeclared variable: " ++ var)

-- Reads variable value from environment.
varsRead :: Vars -> ID_Var -> Val
varsRead vars var = case vars of
  (var',val):vars'
    | var' == var -> if isJust val then fromJust val
                     else error ("varsRead: uninitialized variable: " ++ var)
    | otherwise   -> varsRead vars' var
  []              -> error ("varsRead: undeclared variable: " ++ var)

-- Evaluates expression in environment.
varsEval :: Vars -> Expr -> Val
varsEval vars expr = case expr of
  Const val -> val
  Read var  -> varsRead vars var
  Umn e     -> negate $ varsEval vars e
  Add e1 e2 -> (varsEval vars e1) + (varsEval vars e2)
  Sub e1 e2 -> (varsEval vars e1) - (varsEval vars e2)
  Mul e1 e2 -> (varsEval vars e1) * (varsEval vars e2)
  Div e1 e2 -> (varsEval vars e1) `div` (varsEval vars e2)

-- Set event in environment.
evtsEmit :: Evts -> ID_Evt -> Evts
evtsEmit evts evt = case evts of
  (evt',val'):evts'
    | evt == evt' -> (evt,True):evts'
    | otherwise   -> (evt',val'):(evtsEmit evts' evt)
  []              -> error ("evtsEmit: undeclared event: " ++ evt)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked n stmt = case stmt of
  AwaitExt evt -> True
  AwaitInt evt -> True
  Every evt p  -> True
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
nst1Adv d f = (f p, n, vars, evts)
  where
    (p, n, vars, evts) = nst1 d

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Var' var val Nop, n, vars, evts)     -- var-nop
  = (Nop, n, vars, evts)

nst1 (Var' var val Break, n, vars, evts)   -- var-brk
  = (Break, n, vars, evts)

nst1 (Var' var val p, n, vars, evts)       -- var-adv
  = (Var' var val' p', n', vars', evts')
    where
      (p', n', (_,val'):vars', evts') = nst1Adv (p, n, (var,val):vars, evts) id

nst1 (Evt id Nop, n, vars, evts)           -- evt-nop
  = (Nop, n, vars, evts)

nst1 (Evt id Break, n, vars, evts)         -- evt-brk
  = (Break, n, vars, evts)

nst1 (Evt evt p, n, vars, evts)       -- evt-adv
  = (Evt evt p'', n', vars', evts')
    where
      (p', n', vars', (_,go):evts') = nst1Adv (p, n, vars, (evt,False):evts) id
      p'' | go = bcast evt p'
          | otherwise = p'

nst1 (Write var expr, n, vars, evts)       -- write
  = (Nop, n, varsWrite vars var (varsEval vars expr), evts)

nst1 (EmitInt evt, n, vars, evts)            -- emit-int (pg 6)
  = (CanRun n, n+1, vars, evtsEmit evts evt)

nst1 (CanRun m, n, vars, evts)             -- can-run (pg 6)
  | m==n = (Nop, n, vars, evts)

nst1 (Seq Nop q, n, vars, evts)            -- seq-nop (pg 6)
  = (q, n, vars, evts)

nst1 (Seq Break q, n, vars, evts)          -- seq-brk (pg 6)
  = (Break, n, vars, evts)

nst1 (Seq p q, n, vars, evts)              -- seq-adv (pg 6)
  = nst1Adv (p, n, vars, evts) (\p' -> Seq p' q)

nst1 (If exp p q, n, vars, evts)           -- if-true/false (pg 6)
  | (varsEval vars exp) /= 0 = (p, n, vars, evts)
  | otherwise                = (q, n, vars, evts)

nst1 (Loop' Nop q, n, vars, evts)          -- loop-nop (pg 7)
  = (Loop' q q, n, vars, evts)

nst1 (Loop' Break q, n, vars, evts)        -- loop-brk (pg 7)
  = (Nop, n, vars, evts)

nst1 (Loop' p q, n, vars, evts)            -- loop-adv (pg 7)
  = nst1Adv (p, n, vars, evts) (\p' -> Loop' p' q)

nst1 (And p q, n, vars, evts)              -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, vars, evts)

nst1 (And' Nop q, n, vars, evts)           -- and-nop1 (pg 7)
  = (q, n, vars, evts)

nst1 (And' Break q, n, vars, evts)         -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, vars, evts)

nst1 (And' p Nop, n, vars, evts)           -- and-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> And' p' Nop)
  | otherwise           = (p, n, vars, evts)

nst1 (And' p Break, n, vars, evts)         -- and-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> And' p' Break)
  | otherwise           = (Seq (clear p) Break, n, vars, evts)

nst1 (And' p q, n, vars, evts)             -- and-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> And' p' q)
  | otherwise           = nst1Adv (q, n, vars, evts) (\q' -> And' p q')

nst1 (Or p q, n, vars, evts)               -- or-expd (pg 7)
  = (Or' p (Seq (CanRun n) q), n, vars, evts)

nst1 (Or' Nop q, n, vars, evts)            -- or-nop1 (pg 7)
  = (clear q, n, vars, evts)

nst1 (Or' Break q, n, vars, evts)          -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, vars, evts)

nst1 (Or' p Nop, n, vars, evts)            -- or-nop2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> Or' p' Nop)
  | otherwise           = (clear p, n, vars, evts)

nst1 (Or' p Break, n, vars, evts)          -- or-brk2 (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> Or' p' Break)
  | otherwise           = (Seq (clear p) Break, n, vars, evts)

nst1 (Or' p q, n, vars, evts)              -- or-adv (pg 7)
  | not $ isBlocked n p = nst1Adv (p, n, vars, evts) (\p' -> Or' p' q)
  | otherwise           = nst1Adv (q, n, vars, evts) (\q' -> Or' p q')

nst1 (Error msg, _, _, _) = error ("Runtime error: " ++ msg)

nst1 (p, n, vars, evts)                    -- pop
  | isNstReducible (p,n,vars,evts) = (p, n-1, vars, evts)

--nst1 _ = error "nst1: cannot advance"
nst1 p =  traceShow p (error "nst1: cannot advance")

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstReducible :: Desc -> Bool
isNstReducible desc = case desc of
  (_,     n, _, _) | n>0 -> True
  (Nop,   _, _, _)       -> False
  (Break, _, _, _)       -> False
  (p,     n, _, evts)    -> not $ isBlocked n p

-- Zero or more nested transitions.
-- (pg 6)
nsts :: Desc -> Desc
nsts d
  | not $ isNstReducible d = d
--  | otherwise = traceShow d (nsts $ nst1 d)
  | otherwise = nsts $ nst1 d

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

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, ID_Evt, Vars) -> (Stmt, Vars)
reaction (p, evt, vars) = (p', vars')
  where
    (p', _, vars', _) = nsts (bcast evt p, 0, vars, [])

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
