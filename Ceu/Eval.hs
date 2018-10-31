module Ceu.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Data.Maybe
import Text.Printf
import Debug.Trace

type Lvl = Int

-- Environment.
type Vars = [(ID_Var, Maybe Val)]
type Ints = [(ID_Int, Bool)]
type Outs = [(ID_Ext, Maybe Val)]

-- Description (pg 6).
type Desc = (Stmt, Lvl, Vars, Ints, Outs)

-- Program (pg 5).
data Stmt
  = Int ID_Int Stmt             -- event declaration
  | Write ID_Var Exp            -- assignment statement
  | AwaitExt ID_Ext             -- await external event
  | EmitExt ID_Ext (Maybe Exp)  -- emit internal event
  | AwaitInt ID_Int             -- await internal event
  | EmitInt ID_Int              -- emit internal event
  | Break                       -- loop escape
  | If Exp Stmt Stmt            -- conditional
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
fromGrammar (G.Int id p)      = Int id (fromGrammar p)
fromGrammar (G.Write id exp)  = Write id exp
fromGrammar (G.AwaitExt id)   = AwaitExt id
fromGrammar (G.EmitExt id exp)= EmitExt id exp
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
  Int id stmt          -> printf ":%s %s" id (sP stmt)
  Write var expr       -> printf "%s=%s" var (sE expr)
  AwaitExt ext         -> printf "?%s" ext
  EmitExt ext Nothing  -> printf "!%s" ext
  EmitExt ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitInt int         -> printf "?%s" int
  EmitInt int          -> printf "!%s" int
  Break                -> "break"
  If expr p q          -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq p q              -> printf "%s; %s" (sP p) (sP q)
  Every int p          -> printf "(every %s %s)" int (sP p)
  And p q              -> printf "(%s && %s)" (sP p) (sP q)
  Or p q               -> printf "(%s || %s)" (sP p) (sP q)
  Fin p                -> printf "(fin %s)" (sP p)
  Nop                  -> "nop"
  Error _              -> "err"
  CanRun n             -> printf "@canrun(%d)" n
  Var' var val p
    | isNothing val -> printf "{%s=_: %s}" var (sP p)
    | otherwise     -> printf "{%s=%d: %s}" var (fromJust val) (sP p)
  Loop' p q            -> printf "(%s @loop %s)" (sP p) (sP q)
  And' p q             -> printf "(%s @&& %s)" (sP p) (sP q)
  Or' p q              -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExp
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
varsEval :: Vars -> Exp -> Val
varsEval vars expr = case expr of
  Const val -> val
  Read var  -> varsRead vars var
  Umn e     -> negate $ varsEval vars e
  Add e1 e2 -> (varsEval vars e1) + (varsEval vars e2)
  Sub e1 e2 -> (varsEval vars e1) - (varsEval vars e2)
  Mul e1 e2 -> (varsEval vars e1) * (varsEval vars e2)
  Div e1 e2 -> (varsEval vars e1) `div` (varsEval vars e2)
  Equ e1 e2 -> if (varsEval vars e1) == (varsEval vars e2) then 1 else 0
  Lte e1 e2 -> if (varsEval vars e1) <= (varsEval vars e2) then 1 else 0

-- Set event in environment.
evtsEmit :: Ints -> ID_Int -> Ints
evtsEmit ints int = case ints of
  (int',val'):ints'
    | int == int' -> (int,True):ints'
    | otherwise   -> (int',val'):(evtsEmit ints' int)
  []              -> error ("evtsEmit: undeclared event: " ++ int)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked n stmt = case stmt of
  AwaitExt _   -> True
  AwaitInt _   -> True
  Every _ _    -> True
  CanRun m     -> n > m
  Fin _        -> True
  Seq p _      -> isBlocked n p
  Int _ p      -> isBlocked n p
  Var' _ _ p   -> isBlocked n p
  Loop' p _    -> isBlocked n p
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
  Int _ p      -> clear p
  Var' _ _ p   -> clear p
  Loop' p _    -> clear p
  And' p q     -> Seq (clear p) (clear q)
  Or' p q      -> Seq (clear p) (clear q)
  _            -> error "clear: invalid clear"

-- Helper function used by step in the *-adv rules.
stepAdv :: Desc -> (Stmt -> Stmt) -> Desc
stepAdv d f = (f p, n, vars, ints, outs)
  where
    (p, n, vars, ints, outs) = step d

-- Single nested transition.
-- (pg 6)
step :: Desc -> Desc

step (Var' var val Nop, n, vars, ints, outs)     -- var-nop
  = (Nop, n, vars, ints, outs)

step (Var' var val Break, n, vars, ints, outs)   -- var-brk
  = (Break, n, vars, ints, outs)

step (Var' var val p, n, vars, ints, outs)       -- var-adv
  = (Var' var val' p', n', vars', ints', outs')
    where
      (p', n', (_,val'):vars', ints', outs') = stepAdv (p, n, (var,val):vars, ints, outs) id

step (Int id Nop, n, vars, ints, outs)           -- int-nop
  = (Nop, n, vars, ints, outs)

step (Int id Break, n, vars, ints, outs)         -- int-brk
  = (Break, n, vars, ints, outs)

step (Int int p, n, vars, ints, outs)            -- int-adv
  = (Int int p'', n', vars', ints', outs')
    where
      (p', n', vars', (_,go):ints', outs') = stepAdv (p, n, vars, (int,False):ints, outs) id
      p'' | go = bcast int p'
          | otherwise = p'

step (Write var expr, n, vars, ints, outs)       -- write
  = (Nop, n, varsWrite vars var (varsEval vars expr), ints, outs)

step (EmitExt ext Nothing, n, vars, ints, outs)    -- emit-ext
  = (Nop, n, vars, ints, outs++[(ext,Nothing)])
step (EmitExt ext (Just exp), n, vars, ints, outs) -- emit-ext
  = (Nop, n, vars, ints, outs++[(ext,Just (varsEval vars exp))])

step (EmitInt int, n, vars, ints, outs)          -- emit-int (pg 6)
  = (CanRun n, n+1, vars, evtsEmit ints int, outs)

step (CanRun m, n, vars, ints, outs)             -- can-run (pg 6)
  | m==n = (Nop, n, vars, ints, outs)

step (Seq Nop q, n, vars, ints, outs)            -- seq-nop (pg 6)
  = (q, n, vars, ints, outs)

step (Seq Break q, n, vars, ints, outs)          -- seq-brk (pg 6)
  = (Break, n, vars, ints, outs)

step (Seq p q, n, vars, ints, outs)              -- seq-adv (pg 6)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Seq p' q)

step (If exp p q, n, vars, ints, outs)           -- if-true/false (pg 6)
  | (varsEval vars exp) /= 0 = (p, n, vars, ints, outs)
  | otherwise                = (q, n, vars, ints, outs)

step (Loop' Nop q, n, vars, ints, outs)          -- loop-nop (pg 7)
  = (Loop' q q, n, vars, ints, outs)

step (Loop' Break q, n, vars, ints, outs)        -- loop-brk (pg 7)
  = (Nop, n, vars, ints, outs)

step (Loop' p q, n, vars, ints, outs)            -- loop-adv (pg 7)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Loop' p' q)

step (And p q, n, vars, ints, outs)              -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, vars, ints, outs)

step (And' Nop q, n, vars, ints, outs)           -- and-nop1 (pg 7)
  = (q, n, vars, ints, outs)

step (And' Break q, n, vars, ints, outs)         -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, vars, ints, outs)

step (And' p Nop, n, vars, ints, outs)           -- and-nop2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> And' p' Nop)
  | otherwise           = (p, n, vars, ints, outs)

step (And' p Break, n, vars, ints, outs)         -- and-brk2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> And' p' Break)
  | otherwise           = (Seq (clear p) Break, n, vars, ints, outs)

step (And' p q, n, vars, ints, outs)             -- and-adv (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> And' p' q)
  | otherwise           = stepAdv (q, n, vars, ints, outs) (\q' -> And' p q')

step (Or p q, n, vars, ints, outs)               -- or-expd (pg 7)
  = (Or' p (Seq (CanRun n) q), n, vars, ints, outs)

step (Or' Nop q, n, vars, ints, outs)            -- or-nop1 (pg 7)
  = (clear q, n, vars, ints, outs)

step (Or' Break q, n, vars, ints, outs)          -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, vars, ints, outs)

step (Or' p Nop, n, vars, ints, outs)            -- or-nop2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Or' p' Nop)
  | otherwise           = (clear p, n, vars, ints, outs)

step (Or' p Break, n, vars, ints, outs)          -- or-brk2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Or' p' Break)
  | otherwise           = (Seq (clear p) Break, n, vars, ints, outs)

step (Or' p q, n, vars, ints, outs)              -- or-adv (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Or' p' q)
  | otherwise           = stepAdv (q, n, vars, ints, outs) (\q' -> Or' p q')

step (Error msg, _, _, _, _) = error ("Runtime error: " ++ msg)

step (p, n, vars, ints, outs)                    -- pop
  | isReducible (p,n,vars,ints, outs) = (p, n-1, vars, ints, outs)

--step _ = error "step: cannot advance"
step p =  traceShow p (error "step: cannot advance")

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isReducible :: Desc -> Bool
isReducible desc = case desc of
  (_,     n, _, _, _) | n>0 -> True
  (Nop,   _, _, _, _)       -> False
  (Break, _, _, _, _)       -> False
  (p,     n, _, _, _)    -> not $ isBlocked n p

-- Awakes all trails waiting for the given event.
-- (pg 8, fig 4.i)
bcast :: ID_Evt -> Stmt -> Stmt
bcast e stmt = case stmt of
  AwaitExt e' | e == e' -> Nop
  AwaitInt e' | e == e' -> Nop
  Every e' p  | e == e' -> Seq p (Every e' p)
  Seq p q               -> Seq (bcast e p) q
  Int id p              -> Int id (bcast e p)
  Var' id val p         -> Var' id val (bcast e p)
  Loop' p q             -> Loop' (bcast e p) q
  And' p q              -> And' (bcast e p) (bcast e q)
  Or' p q               -> Or' (bcast e p) (bcast e q)
  _                     -> stmt -- nothing to do

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single external event.
-- (pg 6)
reaction :: Stmt -> ID_Ext -> (Stmt,Outs)
reaction p ext = (p',outs') where (p',_,_,_,outs') = steps (bcast ext p, 0, [], [], [])

steps :: Desc -> Desc
steps d
  | not $ isReducible d = d
  | otherwise = steps $ step d
  -- | otherwise = traceShow d (steps $ step d)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg_Reaction :: G.Stmt -> [a] -> (Stmt->a->(Stmt,Outs)) -> (Val,[Outs])
evalProg_Reaction prog ins reaction -- enclosing block with "ret" that never terminates
  = eP (fromGrammar (G.Var "ret" (G.Seq prog (G.AwaitExt "FOREVER")))) ins []
  where
    --eP :: Stmt -> [a] -> [Outs] -> (Val,[Outs])
    eP prog ins outss = case prog of
      (Var' "ret" val (AwaitExt "FOREVER"))
        | not (null ins) -> error "evalProg: pending inputs"
        | isNothing val  -> error "evalProg: no return"
        | otherwise      -> ((fromJust val), outss)
      _
        | null ins       -> error "evalProg: program didn't terminate"
        | otherwise      -> eP prog' (tail ins) (outss++[outs']) where
                               (prog',outs') = reaction prog (head ins)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: G.Stmt -> [ID_Ext] -> (Val,[Outs])
evalProg prog ins = evalProg_Reaction prog ("BOOT":ins) reaction
