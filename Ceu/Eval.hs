module Ceu.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann (annz)
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt     as G
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
  | If       Exp Stmt Stmt              -- conditional
  | Seq      Stmt Stmt                  -- sequence
  | Nop                                 -- dummy statement (internal)
  deriving (Eq, Show)

infixr 1 `Seq`

fromGrammar :: G.Stmt -> Stmt
fromGrammar (G.Class _ _ _ _ p) = fromGrammar p
fromGrammar (G.Inst _ _ _ _ p)  = fromGrammar p
fromGrammar (G.Data _ _ _ _ _ p)= fromGrammar p
fromGrammar (G.Var _ id _ p)    = Var (id,Nothing) (fromGrammar p)
fromGrammar (G.Func _ _ _ p)    = (fromGrammar p)
fromGrammar (G.FuncI _ _ _ _ _) = error "not implemented"
fromGrammar (G.Write _ (LVar id) exp) = Write id exp
fromGrammar (G.If _ exp p1 p2)  = If exp (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq _ p1 p2)     = Seq (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Nop _)           = Nop

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
  Seq p _      -> isBlocked n p
  _            -> False

isBlockedNop n Nop = True
isBlockedNop n p   = isBlocked n p

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  Var _ p      -> clear p
  Seq p _      -> clear p
  Nop          -> Nop -- because of blocked (Par Nop Nop)
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

step (Var vv p, n, vars, ints, outs)             -- var-adv
  = (Var vv' p', n', vars', ints', outs')
    where
      (p', n', vv':vars', ints', outs') = stepAdv (p, n, vv:vars, ints, outs) id

step (Write var expr, n, vars, ints, outs)       -- write
  = (Nop, n, varsWrite vars var (varsEval vars expr), ints, outs)

step (Seq Nop q, n, vars, ints, outs)            -- seq-nop (pg 6)
  = (q, n, vars, ints, outs)

step (Seq p q, n, vars, ints, outs)              -- seq-adv (pg 6)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Seq p' q)

step (If exp p q, n, vars, ints, outs)           -- if-true/false (pg 6)
  | (varsEval vars exp) /= 0 = (p, n, vars, ints, outs)
  | otherwise                = (q, n, vars, ints, outs)

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
  (p,     n, _, _, _)       -> not $ isBlocked n p

-- Awakes all trails waiting for the given event.
-- (pg 8, fig 4.i)
bcast :: ID -> Vars -> Stmt -> Stmt
bcast e vars stmt = case stmt of
  Var vv p              -> Var vv (bcast e (vv:vars) p)
  Seq p q               -> Seq (bcast e vars p) q
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
      (Var ("_ret",val) Nop)
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
  let (es,p) = Check.compile (True) prog in
    if es == [] then
      run p ("BOOT":ins) reaction
    else
      Left es
