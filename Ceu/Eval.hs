module Ceu.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann (annz)
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt     as G
import qualified Ceu.Grammar.Simplify as S
import qualified Ceu.Grammar.Check    as Check
import Data.Maybe
import Text.Printf
import Debug.Trace

type Lvl = Int

-- Environment.
type Vars = [(ID_Var, Maybe Val)]
type Evts = [(ID_Evt, Bool)]
type Outs = [(ID_Out, Maybe Val)]

-- Description (pg 6).
type Desc = (Stmt, Lvl, Vars, Evts, Outs)

-- Program (pg 5).
data Stmt
  = Var      (ID_Var,Maybe Val) Stmt    -- block with environment store
  | Evt      ID_Evt Stmt                -- event declaration
  | Write    ID_Var Exp                 -- assignment statement
  | AwaitInp ID_Inp                     -- await external event
  | EmitExt  ID_Ext Exp                 -- emit external event
  | AwaitEvt ID_Evt                     -- await internal event
  | EmitEvt  ID_Evt                     -- emit internal event
  | If       Exp Stmt Stmt              -- conditional
  | Seq      Stmt Stmt                  -- sequence
  | Every    ID Stmt                    -- event iteration
  | Par      Stmt Stmt                  -- par statement
  | Pause    ID_Var Stmt                -- pause/suspend statement
  | Fin      Stmt                       -- finalization statement
  | Trap     Stmt                       -- enclose escape
  | Escape   Int                        -- escape N traps
  | Nop                                 -- dummy statement (internal)
  | Halt                                -- halt (await FOREVER)
  | Error    String                     -- generate runtime error (for testing purposes)
  | CanRun Lvl                          -- wait for stack level (internal)
  | Loop' Stmt Stmt                     -- unrolled Loop (internal)
  | Par' Stmt Stmt                      -- unrolled Par (internal)
  deriving (Eq, Show)

infixr 1 `Seq`
infixr 0 `Par`

fromGrammar :: G.Stmt -> Stmt
fromGrammar (G.Data _ _ _ _ _ p)= fromGrammar p
fromGrammar (G.Var _ id _ p)    = Var (id,Nothing) (fromGrammar p)
fromGrammar (G.Inp _ _ p)       = (fromGrammar p)
fromGrammar (G.Out _ _ _ p)     = (fromGrammar p)
fromGrammar (G.Evt _ id p)      = Evt id (fromGrammar p)
fromGrammar (G.Func _ _ _ p)    = (fromGrammar p)
fromGrammar (G.FuncI _ _ _ _ _) = error "not implemented"
fromGrammar (G.Write _ (LVar id) exp) = Write id exp
fromGrammar (G.AwaitInp _ id)   = AwaitInp id
fromGrammar (G.EmitExt _ id exp)= EmitExt id exp
fromGrammar (G.AwaitEvt _ id)   = AwaitEvt id
fromGrammar (G.EmitEvt _ id)    = EmitEvt id
fromGrammar (G.If _ exp p1 p2)  = If exp (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq _ p1 p2)     = Seq (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Loop _ p)        = Loop' (fromGrammar p) (fromGrammar p)
fromGrammar (G.Every _ id p)    = Every id (fromGrammar p)
fromGrammar (G.Par _ p1 p2)     = Par (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Pause _ var p)   = Pause var (fromGrammar p)
fromGrammar (G.Fin _ p)         = Fin (fromGrammar p)
fromGrammar (G.Trap _ p)        = Trap (fromGrammar p)
fromGrammar (G.Escape _ n)      = Escape n
fromGrammar (G.Halt _)          = Halt
fromGrammar (G.Nop _)           = Nop
fromGrammar (G.Error _ msg)     = Error msg

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
  Const _ val     -> val
  Read  _ var     -> varsRead vars var
  Call  _ "negate" e -> negate $ varsEval vars e
  Call  _ "+"  (Tuple _ [e1,e2]) -> (varsEval vars e1) + (varsEval vars e2)
  Call  _ "-"  (Tuple _ [e1,e2]) -> (varsEval vars e1) - (varsEval vars e2)
  Call  _ "*"  (Tuple _ [e1,e2]) -> (varsEval vars e1) * (varsEval vars e2)
  Call  _ "/"  (Tuple _ [e1,e2]) -> (varsEval vars e1) `div` (varsEval vars e2)
  Call  _ "==" (Tuple _ [e1,e2]) -> if (varsEval vars e1) == (varsEval vars e2) then 1 else 0
  Call  _ "<=" (Tuple _ [e1,e2]) -> if (varsEval vars e1) <= (varsEval vars e2) then 1 else 0

-- Set event in environment.
evtsEmit :: Evts -> ID_Evt -> Evts
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
  Evt _ p      -> isBlocked n p
  AwaitInp _   -> True
  AwaitEvt _   -> True
  Every _ _    -> True
  CanRun m     -> n > m
  Pause _ p    -> isBlocked n p
  Fin _        -> True
  Seq p _      -> isBlocked n p
  Trap p       -> isBlockedNop n p
  Halt         -> True
  Loop' p _    -> isBlocked n p
  Par' p q     -> isBlockedNop n p && isBlockedNop n q
  _            -> False

isBlockedNop n Nop = True
isBlockedNop n p   = isBlocked n p

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  Var _ p      -> clear p
  Evt _ p      -> clear p
  AwaitInp _   -> Nop
  AwaitEvt _   -> Nop
  Every _ _    -> Nop
  CanRun _     -> Nop
  Fin p        -> p
  Pause _ p    -> clear p
  Seq p _      -> clear p
  Trap p       -> clear p
  Loop' p _    -> clear p
  Par' p q     -> Seq (clear p) (clear q)
  Nop          -> Nop -- because of blocked (Par Nop Nop)
  Halt         -> Nop
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

step (Evt id Nop, n, vars, ints, outs)           -- int-nop
  = (Nop, n, vars, ints, outs)

step (Evt id (Escape k), n, vars, ints, outs)    -- int-escape
  = (Escape k, n, vars, ints, outs)

step (Evt int p, n, vars, ints, outs)            -- int-adv
  = (Evt int p'', n', vars', ints', outs')
    where
      (p', n', vars', (_,go):ints', outs') = stepAdv (p, n, vars, (int,False):ints, outs) id
      p'' | go = bcast int vars p'
          | otherwise = p'

step (Write var expr, n, vars, ints, outs)       -- write
  = (Nop, n, varsWrite vars var (varsEval vars expr), ints, outs)

step (EmitExt ext (Unit _), n, vars, ints, outs)    -- emit-ext
  = (Nop, n, vars, ints, outs++[(ext,Nothing)])
step (EmitExt ext exp, n, vars, ints, outs) -- emit-ext
  = (Nop, n, vars, ints, outs++[(ext,Just (varsEval vars exp))])

step (EmitEvt int, n, vars, ints, outs)          -- emit-int (pg 6)
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
  = (Escape k, n, vars, ints, outs)

step (Loop' p q, n, vars, ints, outs)            -- loop-adv (pg 7)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Loop' p' q)

step (Par p q, n, vars, ints, outs)              -- par-expd (pg 7)
  = (Par' p (Seq (CanRun n) q ), n, vars, ints, outs)

step (Par' (Escape k) q, n, vars, ints, outs)    -- and escape1 (pg 7)
  = (Seq (clear q) (Escape k), n, vars, ints, outs)

step (Par' p (Escape k), n, vars, ints, outs)    -- and-escape2 (pg 7)
  | not $ isBlockedNop n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' p' (Escape k))
  | otherwise              = (Seq (clear p) (Escape k), n, vars, ints, outs)

step (Par' p q, n, vars, ints, outs)             -- and-adv (pg 7)
  | not $ isBlockedNop n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' p' q)
  | otherwise              = stepAdv (q, n, vars, ints, outs) (\q' -> Par' p q')

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

step _ = error "step: cannot advance"
--step p =  traceShow p (error "step: cannot advance")

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
bcast :: ID -> Vars -> Stmt -> Stmt
bcast e vars stmt = case stmt of
  Var vv p              -> Var vv (bcast e (vv:vars) p)
  Evt id p              -> Evt id (bcast e vars p)
  AwaitInp e' | e == e' -> Nop
  AwaitEvt e' | e == e' -> Nop
  Every e' p  | e == e' -> Seq p (Every e' p)
  Seq p q               -> Seq (bcast e vars p) q
  Trap p                -> Trap (bcast e vars p)
  Loop' p q             -> Loop' (bcast e vars p) q
  Par' p q              -> Par' (bcast e vars p) (bcast e vars q)
  Pause var p           -> Pause var (if (varsEval vars (Read annz var)) == 1 then p else (bcast e vars p))
  _                     -> stmt -- nothing to do

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single external event.
-- (pg 6)
reaction :: Stmt -> ID_Inp -> (Stmt, Outs)
reaction p ext = (p',outs') where (p',_,_,_,outs') = steps (bcast ext [] p, 0, [], [], [])

steps :: Desc -> Desc
steps d
  | not $ isReducible d = d
  | otherwise = steps $ step d
  -- | otherwise = traceShow d (steps $ step d)

type Result = Either Errors (Val,[Outs])

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
run :: G.Stmt -> [a] -> (Stmt -> a -> (Stmt, Outs)) -> Result
run prog ins reaction = eP (fromGrammar prog) ins []
  where
    --eP :: Stmt -> [a] -> [Outs] -> (Val,[Outs])
    eP prog ins outss = case prog of
      (Var ("_ret",val) Halt)
        | not (null ins) -> Left ["pending inputs"]
        | isNothing val  -> Left ["no return value"]
        | otherwise      -> Right ((fromJust val), outss)
      _
        | null ins       -> Left ["program didn't terminate"]
        | otherwise      -> eP prog' (tail ins) (outss++[outs']) where
                               (prog',outs') = reaction prog (head ins)

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
compile_run :: G.Stmt -> [ID_Inp] -> Result
compile_run prog ins =
  let (es,p) = Check.compile (True,True,True) prog in
    if es == [] then
      run p ("BOOT":ins) reaction
    else
      Left es
