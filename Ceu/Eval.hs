module Ceu.Eval where

import Ceu.Globals
import qualified Ceu.Grammar          as G
import qualified Ceu.Grammar.Simplify as S
import qualified Ceu.Grammar.Check    as Check
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
  = Var (ID_Var,Maybe Val) Stmt -- block with environment store
  | Int ID_Int Stmt             -- event declaration
  | Write ID_Var Exp            -- assignment statement
  | AwaitExt ID_Ext             -- await external event
  | EmitExt ID_Ext (Maybe Exp)  -- emit internal event
  | AwaitInt ID_Int             -- await internal event
  | EmitInt ID_Int              -- emit internal event
  | If Exp Stmt Stmt            -- conditional
  | Seq Stmt Stmt               -- sequence
  | Every ID_Evt Stmt           -- event iteration
  | Par Stmt Stmt               -- par statement
  | Pause ID_Var Stmt           -- pause/suspend statement
  | Fin Stmt                    -- finalization statement
  | Trap Stmt                   -- enclose escape
  | Escape Int                  -- escape N traps
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing purposes)
  | CanRun Lvl                  -- wait for stack level (internal)
  | Loop' Stmt Stmt             -- unrolled Loop (internal)
  | Par' Stmt Stmt              -- unrolled Par (internal)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Par`                  -- `Par` associates to the right

fromGrammar :: G.Stmt -> Stmt
fromGrammar (G.Var id p)      = Var (id,Nothing) (fromGrammar p)
fromGrammar (G.Int id p)      = Int id (fromGrammar p)
fromGrammar (G.Write id exp)  = Write id exp
fromGrammar (G.AwaitExt id)   = AwaitExt id
fromGrammar (G.EmitExt id exp)= EmitExt id exp
fromGrammar (G.AwaitInt id)   = AwaitInt id
fromGrammar (G.EmitInt id)    = EmitInt id
fromGrammar (G.If exp p1 p2)  = If exp (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq p1 p2)     = Seq (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Loop p)        = Loop' (fromGrammar p) (fromGrammar p)
fromGrammar (G.Every id p)    = Every id (fromGrammar p)
fromGrammar (G.Par p1 p2)     = Par (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Pause var p)   = Pause var (fromGrammar p)
fromGrammar (G.Fin p)         = Fin (fromGrammar p)
fromGrammar (G.Trap p)        = Trap (fromGrammar p)
fromGrammar (G.Escape n)      = Escape n
fromGrammar G.Nop             = Nop
fromGrammar (G.Error msg)     = Error msg

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Var (var,val) p
    | isNothing val    -> printf "{%s=_: %s}" var (sP p)
    | otherwise        -> printf "{%s=%d: %s}" var (fromJust val) (sP p)
  Int id stmt          -> printf ":%s %s" id (sP stmt)
  Write var expr       -> printf "%s=%s" var (sE expr)
  AwaitExt ext         -> printf "?%s" ext
  EmitExt ext Nothing  -> printf "!%s" ext
  EmitExt ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitInt int         -> printf "?%s" int
  EmitInt int          -> printf "!%s" int
  If expr p q          -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq p q              -> printf "%s; %s" (sP p) (sP q)
  Every int p          -> printf "(every %s %s)" int (sP p)
  Par p q              -> printf "(%s || %s)" (sP p) (sP q)
  Pause var p          -> printf "(pause %s %s)" var (sP p)
  Fin p                -> printf "(fin %s)" (sP p)
  Trap p               -> printf "(trap %s)" (sP p)
  Escape n             -> printf "(escape %d)" n
  Nop                  -> "nop"
  Error _              -> "err"
  CanRun n             -> printf "@canrun(%d)" n
  Loop' p q            -> printf "(%s @loop %s)" (sP p) (sP q)
  Par' p q             -> printf "(%s @|| %s)" (sP p) (sP q)
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
  Var _ p      -> isBlocked n p
  Int _ p      -> isBlocked n p
  AwaitExt _   -> True
  AwaitInt _   -> True
  Every _ _    -> True
  CanRun m     -> n > m
  Pause _ p    -> isBlocked n p
  Fin _        -> True
  Seq p _      -> isBlocked n p
  Trap p       -> isBlocked n p
  Loop' p _    -> isBlocked n p
  Par' p q     -> isBlocked n p && isBlocked n q
  _            -> False

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  Var _ p      -> clear p
  Int _ p      -> clear p
  AwaitExt _   -> Nop
  AwaitInt _   -> Nop
  Every _ _    -> Nop
  CanRun _     -> Nop
  Fin p        -> p
  Pause _ p    -> clear p
  Seq p _      -> clear p
  Trap p       -> clear p
  Loop' p _    -> clear p
  Par' p q     -> Seq (clear p) (clear q)
  _            -> error "clear: invalid clear"

-- Helper function used by step in the *-adv rules.
stepAdv :: Desc -> (Stmt -> Stmt) -> Desc
stepAdv d f = (f p, n, vars, ints, outs)
  where
    (p, n, vars, ints, outs) = step d

-- Single nested transition.
-- (pg 6)
step :: Desc -> Desc

step (Var _ Nop, n, vars, ints, outs)            -- var-nop
  = (Nop, n, vars, ints, outs)

step (Var _ (Escape k), n, vars, ints, outs)     -- var-escape
  = (Escape k, n, vars, ints, outs)

step (Var vv p, n, vars, ints, outs)             -- var-adv
  = (Var vv' p', n', vars', ints', outs')
    where
      (p', n', vv':vars', ints', outs') = stepAdv (p, n, vv:vars, ints, outs) id

step (Int id Nop, n, vars, ints, outs)           -- int-nop
  = (Nop, n, vars, ints, outs)

step (Int id (Escape k), n, vars, ints, outs)    -- int-escape
  = ((Escape k), n, vars, ints, outs)

step (Int int p, n, vars, ints, outs)            -- int-adv
  = (Int int p'', n', vars', ints', outs')
    where
      (p', n', vars', (_,go):ints', outs') = stepAdv (p, n, vars, (int,False):ints, outs) id
      p'' | go = bcast int vars p'
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

step (Seq (Escape k) q, n, vars, ints, outs)     -- seq-escape (pg 6)
  = (Escape k, n, vars, ints, outs)

step (Seq p q, n, vars, ints, outs)              -- seq-adv (pg 6)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Seq p' q)

step (If exp p q, n, vars, ints, outs)           -- if-true/false (pg 6)
  | (varsEval vars exp) /= 0 = (p, n, vars, ints, outs)
  | otherwise                = (q, n, vars, ints, outs)

step (Loop' Nop q, n, vars, ints, outs)          -- loop-nop (pg 7)
  = (Loop' q q, n, vars, ints, outs)

step (Loop' (Escape k) q, n, vars, ints, outs)   -- loop-escape (pg 7)
  = ((Escape k), n, vars, ints, outs)

step (Loop' p q, n, vars, ints, outs)            -- loop-adv (pg 7)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Loop' p' q)

step (Par p q, n, vars, ints, outs)              -- par-expd (pg 7)
  = (Par' p (Seq (CanRun n) q), n, vars, ints, outs)

step (Par' (Escape k) q, n, vars, ints, outs)    -- and escape1 (pg 7)
  = (Seq (clear q) (Escape k), n, vars, ints, outs)

step (Par' p (Escape k), n, vars, ints, outs)    -- and-escape2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' p' (Escape k))
  | otherwise           = (Seq (clear p) (Escape k), n, vars, ints, outs)

step (Par' p q, n, vars, ints, outs)             -- and-adv (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' p' q)
  | otherwise           = stepAdv (q, n, vars, ints, outs) (\q' -> Par' p q')

step (Pause var Nop, n, vars, ints, outs)        -- pause-nop
  = (Nop, n, vars, ints, outs)
step (Pause var (Escape k), n, vars, ints, outs) -- pause-break
  = (Escape k, n, vars, ints, outs)
step (Pause var p, n, vars, ints, outs)          -- pause-adv
  = stepAdv (p, n, vars, ints, outs) (\p' -> Pause var p')

step (Trap (Escape k), n, vars, ints, outs)      -- trap-escape
  | k == 0    = (Nop, n, vars, ints, outs)
  | otherwise = (Escape (k-1), n, vars, ints, outs)
step (Trap p, n, vars, ints, outs)                -- trap-adv
  = stepAdv (p, n, vars, ints, outs) (\p' -> Trap p')

step (Error msg, _, _, _, _) = error ("Runtime error: " ++ msg)

step (p, n, vars, ints, outs)                    -- pop
  | isReducible (p,n,vars,ints, outs) = (p, n-1, vars, ints, outs)

step p =  error $ "step: cannot advance" ++ "\n" ++ (show p)

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isReducible :: Desc -> Bool
isReducible desc = case desc of
  (_,     n, _, _, _) | n>0 -> True
  (Nop,   _, _, _, _)       -> False
  (Escape _, _, _, _, _)    -> False
  (p,     n, _, _, _)       -> not $ isBlocked n p

-- Awakes all trails waiting for the given event.
-- (pg 8, fig 4.i)
bcast :: ID_Evt -> Vars -> Stmt -> Stmt
bcast e vars stmt = case stmt of
  Var vv p              -> Var vv (bcast e (vv:vars) p)
  Int id p              -> Int id (bcast e vars p)
  AwaitExt e' | e == e' -> Nop
  AwaitInt e' | e == e' -> Nop
  Every e' p  | e == e' -> Seq p (Every e' p)
  Seq p q               -> Seq (bcast e vars p) q
  Trap p                -> Trap (bcast e vars p)
  Loop' p q             -> Loop' (bcast e vars p) q
  Par' p q              -> Par' (bcast e vars p) (bcast e vars q)
  Pause var p           -> Pause var (if (varsEval vars (Read var)) == 1 then p else (bcast e vars p))
  _                     -> stmt -- nothing to do

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single external event.
-- (pg 6)
reaction :: Stmt -> ID_Ext -> (Stmt,Outs)
reaction p ext = (p',outs') where (p',_,_,_,outs') = steps (bcast ext [] p, 0, [], [], [])

steps :: Desc -> Desc
steps d
  | not $ isReducible d = d
  | otherwise = steps $ step d
  -- | otherwise = traceShow d (steps $ step d)

data Result = Success (Val,[Outs]) | Fail Errors
  deriving (Show, Eq)

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
run :: G.Stmt -> [a] -> (Stmt->a->(Stmt,Outs)) -> Result
run prog ins reaction = eP (fromGrammar prog) ins []
  where
    --eP :: Stmt -> [a] -> [Outs] -> (Val,[Outs])
    eP prog ins outss = case prog of
      (Var ("_ret",val) (AwaitExt "FOREVER"))
        | not (null ins) -> Fail ["pending inputs"]
        | isNothing val  -> Fail ["no return value"]
        | otherwise      -> Success ((fromJust val), outss)
      _
        | null ins       -> Fail ["program didn't terminate"]
        | otherwise      -> eP prog' (tail ins) (outss++[outs']) where
                               (prog',outs') = reaction prog (head ins)

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
compile_run :: G.Stmt -> [ID_Ext] -> Result
compile_run prog ins =
  let (es,p) = Check.compile (True,True) prog in
    if es == [] then
      run p ("BOOT":ins) reaction
    else
      Fail es
