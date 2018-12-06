module Ceu.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt        as G
import qualified Ceu.Grammar.Simplify    as S
import qualified Ceu.Grammar.Check.Check as Check
import Data.Maybe
import Text.Printf
import Debug.Trace

type Lvl = Int

-- Environment.
type Vars = [(ID_Var, Maybe Val)]
type Ints = [(ID_Int, Bool)]
type Outs = [(ID_Ext, Maybe Val)]

-- Description (pg 6).
type Desc ann = (Stmt ann, Lvl, Vars, Ints, Outs)

-- Program (pg 5).
data Stmt ann
  = Var      ann (ID_Var,Maybe Val) (Stmt ann)   -- block with environment store
  | Int      ann ID_Int (Stmt ann)               -- event declaration
  | Write    ann ID_Var (Exp ann)                -- assignment statement
  | AwaitExt ann ID_Ext                          -- await external event
  | EmitExt  ann ID_Ext (Maybe (Exp ann))        -- emit internal event
  | AwaitInt ann ID_Int                          -- await internal event
  | EmitInt  ann ID_Int                          -- emit internal event
  | If       ann (Exp ann) (Stmt ann) (Stmt ann) -- conditional
  | Seq      ann (Stmt ann) (Stmt ann)           -- sequence
  | Every    ann ID_Evt (Stmt ann)               -- event iteration
  | Par      ann (Stmt ann) (Stmt ann)           -- par statement
  | Pause    ann ID_Var (Stmt ann)               -- pause/suspend statement
  | Fin      ann (Stmt ann)                      -- finalization statement
  | Trap     ann (Stmt ann)                      -- enclose escape
  | Escape   ann Int                             -- escape N traps
  | Nop      ann                                 -- dummy statement (internal)
  | Error    ann String                          -- generate runtime error (for testing purposes)
  | CanRun ann Lvl                               -- wait for stack level (internal)
  | Loop' ann (Stmt ann) (Stmt ann)              -- unrolled Loop (internal)
  | Par' ann (Stmt ann) (Stmt ann)               -- unrolled Par (internal)
  deriving (Eq, Show)

sSeq a b = Seq () a b
sPar a b = Par () a b

infixr 1 `sSeq`
infixr 0 `sPar`

getAnn :: Stmt ann -> ann
getAnn (Var      z _ _)   = z
getAnn (Int      z _ _)   = z
getAnn (Write    z _ _)   = z
getAnn (AwaitExt z _)     = z
getAnn (EmitExt  z _ _)   = z
getAnn (AwaitInt z _)     = z
getAnn (EmitInt  z _)     = z
getAnn (If       z _ _ _) = z
getAnn (Seq      z _ _)   = z
getAnn (Every    z _ _)   = z
getAnn (Par      z _ _)   = z
getAnn (Pause    z _ _)   = z
getAnn (Fin      z _)     = z
getAnn (Trap     z _)     = z
getAnn (Escape   z _)     = z
getAnn (Nop      z)       = z
getAnn (Error    z _)     = z
getAnn (CanRun   z _)     = z
getAnn (Loop'    z _ _)   = z
getAnn (Par'     z _ _)   = z

fromGrammar :: (G.Stmt ann) -> (Stmt ann)
fromGrammar (G.Var z id p)      = Var z (id,Nothing) (fromGrammar p)
fromGrammar (G.Int z id p)      = Int z id (fromGrammar p)
fromGrammar (G.Write z id exp)  = Write z id exp
fromGrammar (G.AwaitExt z id)   = AwaitExt z id
fromGrammar (G.EmitExt z id exp)= EmitExt z id exp
fromGrammar (G.AwaitInt z id)   = AwaitInt z id
fromGrammar (G.EmitInt z id)    = EmitInt z id
fromGrammar (G.If z exp p1 p2)  = If z exp (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Seq z p1 p2)     = Seq z (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Loop z p)        = Loop' z (fromGrammar p) (fromGrammar p)
fromGrammar (G.Every z id p)    = Every z id (fromGrammar p)
fromGrammar (G.Par z p1 p2)     = Par z (fromGrammar p1) (fromGrammar p2)
fromGrammar (G.Pause z var p)   = Pause z var (fromGrammar p)
fromGrammar (G.Fin z p)         = Fin z (fromGrammar p)
fromGrammar (G.Trap z p)        = Trap z (fromGrammar p)
fromGrammar (G.Escape z n)      = Escape z n
fromGrammar (G.Nop z)           = Nop z
fromGrammar (G.Error z msg)     = Error z msg

-- Shows program.
showProg :: (Stmt ann) -> String
showProg stmt = case stmt of
  Var _ (var,val) p
    | isNothing val      -> printf "{%s=_: %s}" var (sP p)
    | otherwise          -> printf "{%s=%d: %s}" var (fromJust val) (sP p)
  Int _ id stmt          -> printf ":%s %s" id (sP stmt)
  Write _ var expr       -> printf "%s=%s" var (sE expr)
  AwaitExt _ ext         -> printf "?%s" ext
  EmitExt _ ext Nothing  -> printf "!%s" ext
  EmitExt _ ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitInt _ int         -> printf "?%s" int
  EmitInt _ int          -> printf "!%s" int
  If _ expr p q          -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq _ p q              -> printf "%s; %s" (sP p) (sP q)
  Every _ int p          -> printf "(every %s %s)" int (sP p)
  Par _ p q              -> printf "(%s || %s)" (sP p) (sP q)
  Pause _ var p          -> printf "(pause %s %s)" var (sP p)
  Fin _ p                -> printf "(fin %s)" (sP p)
  Trap _ p               -> printf "(trap %s)" (sP p)
  Escape _ n             -> printf "(escape %d)" n
  Nop _                  -> "nop"
  Error _ _              -> "err"
  CanRun _ n             -> printf "@canrun(%d)" n
  Loop' _ p q            -> printf "(%s @loop %s)" (sP p) (sP q)
  Par' _ p q             -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExp
    sP = showProg

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
varsEval :: Vars -> (Exp ann) -> Val
varsEval vars expr = case expr of
  Const _ val   -> val
  Read  _ var   -> varsRead vars var
  Umn   _ e     -> negate $ varsEval vars e
  Add   _ e1 e2 -> (varsEval vars e1) + (varsEval vars e2)
  Sub   _ e1 e2 -> (varsEval vars e1) - (varsEval vars e2)
  Mul   _ e1 e2 -> (varsEval vars e1) * (varsEval vars e2)
  Div   _ e1 e2 -> (varsEval vars e1) `div` (varsEval vars e2)
  Equ   _ e1 e2 -> if (varsEval vars e1) == (varsEval vars e2) then 1 else 0
  Lte   _ e1 e2 -> if (varsEval vars e1) <= (varsEval vars e2) then 1 else 0

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
isBlocked :: Lvl -> (Stmt ann) -> Bool
isBlocked n stmt = case stmt of
  Var _ _ p      -> isBlocked n p
  Int _ _ p      -> isBlocked n p
  AwaitExt _ _   -> True
  AwaitInt _ _   -> True
  Every _ _ _    -> True
  CanRun _ m     -> n > m
  Pause _ _ p    -> isBlocked n p
  Fin _ _        -> True
  Seq _ p _      -> isBlocked n p
  Trap _ p       -> isBlocked n p
  Loop' _ p _    -> isBlocked n p
  Par' _ p q     -> isBlocked n p && isBlocked n q
  _              -> False

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: (Stmt ann) -> (Stmt ann)
clear stmt = case stmt of
  Var _ _ p      -> clear p
  Int _ _ p      -> clear p
  AwaitExt z _   -> Nop z
  AwaitInt z _   -> Nop z
  Every z _ _    -> Nop z
  CanRun z _     -> Nop z
  Fin _ p        -> p
  Pause _ _ p    -> clear p
  Seq _ p _      -> clear p
  Trap _ p       -> clear p
  Loop' _ p _    -> clear p
  Par' z p q     -> Seq z (clear p) (clear q)
  _              -> error "clear: invalid clear"

-- Helper function used by step in the *-adv rules.
stepAdv :: Desc ann -> (Stmt ann -> Stmt ann) -> Desc ann
stepAdv d f = (f p, n, vars, ints, outs)
  where
    (p, n, vars, ints, outs) = step d

-- Single nested transition.
-- (pg 6)
step :: Desc ann -> Desc ann

step (Var _ _ s@(Nop _), n, vars, ints, outs)            -- var-nop
  = (s, n, vars, ints, outs)

step (Var _ _ s@(Escape z k), n, vars, ints, outs)     -- var-escape
  = (s, n, vars, ints, outs)

step (Var z vv p, n, vars, ints, outs)             -- var-adv
  = (Var z vv' p', n', vars', ints', outs')
    where
      (p', n', vv':vars', ints', outs') = stepAdv (p, n, vv:vars, ints, outs) id

step (Int _ id s@(Nop _), n, vars, ints, outs)           -- int-nop
  = (s, n, vars, ints, outs)

step (Int _ id s@(Escape _ _), n, vars, ints, outs)    -- int-escape
  = (s, n, vars, ints, outs)

step (Int z int p, n, vars, ints, outs)            -- int-adv
  = (Int z int p'', n', vars', ints', outs')
    where
      (p', n', vars', (_,go):ints', outs') = stepAdv (p, n, vars, (int,False):ints, outs) id
      p'' | go = bcast int vars p'
          | otherwise = p'

step (Write z var expr, n, vars, ints, outs)       -- write
  = (Nop z, n, varsWrite vars var (varsEval vars expr), ints, outs)

step (EmitExt z ext Nothing, n, vars, ints, outs)    -- emit-ext
  = (Nop z, n, vars, ints, outs++[(ext,Nothing)])
step (EmitExt z ext (Just exp), n, vars, ints, outs) -- emit-ext
  = (Nop z, n, vars, ints, outs++[(ext,Just (varsEval vars exp))])

step (EmitInt z int, n, vars, ints, outs)          -- emit-int (pg 6)
  = (CanRun z n, n+1, vars, evtsEmit ints int, outs)

step (CanRun z m, n, vars, ints, outs)             -- can-run (pg 6)
  | m==n = (Nop z, n, vars, ints, outs)

step (Seq _ (Nop _) q, n, vars, ints, outs)            -- seq-nop (pg 6)
  = (q, n, vars, ints, outs)

step (Seq _ s@(Escape _ _) q, n, vars, ints, outs)     -- seq-escape (pg 6)
  = (s, n, vars, ints, outs)

step (Seq z p q, n, vars, ints, outs)              -- seq-adv (pg 6)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Seq z p' q)

step (If _ exp p q, n, vars, ints, outs)           -- if-true/false (pg 6)
  | (varsEval vars exp) /= 0 = (p, n, vars, ints, outs)
  | otherwise                = (q, n, vars, ints, outs)

step (Loop' z (Nop _) q, n, vars, ints, outs)          -- loop-nop (pg 7)
  = (Loop' z q q, n, vars, ints, outs)

step (Loop' _ s@(Escape _ _) q, n, vars, ints, outs)   -- loop-escape (pg 7)
  = (s, n, vars, ints, outs)

step (Loop' z p q, n, vars, ints, outs)            -- loop-adv (pg 7)
  = stepAdv (p, n, vars, ints, outs) (\p' -> Loop' z p' q)

step (Par z p q, n, vars, ints, outs)              -- par-expd (pg 7)
  = (Par' z (Seq z p (AwaitExt z "FOREVER")) (Seq z (CanRun z n) (Seq z q (AwaitExt z "FOREVER"))), n, vars, ints, outs)

step (Par' z s@(Escape _ _) q, n, vars, ints, outs)    -- and escape1 (pg 7)
  = (Seq z (clear q) s, n, vars, ints, outs)

step (Par' z p s@(Escape _ _), n, vars, ints, outs)    -- and-escape2 (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' z p' s)
  | otherwise           = (Seq z (clear p) s, n, vars, ints, outs)

step (Par' z p q, n, vars, ints, outs)             -- and-adv (pg 7)
  | not $ isBlocked n p = stepAdv (p, n, vars, ints, outs) (\p' -> Par' z p' q)
  | otherwise           = stepAdv (q, n, vars, ints, outs) (\q' -> Par' z p q')

step (Pause _ var s@(Nop _), n, vars, ints, outs)        -- pause-nop
  = (s, n, vars, ints, outs)
step (Pause _ var s@(Escape _ _), n, vars, ints, outs) -- pause-break
  = (s, n, vars, ints, outs)
step (Pause z var p, n, vars, ints, outs)          -- pause-adv
  = stepAdv (p, n, vars, ints, outs) (\p' -> Pause z var p')

step (Trap z (Escape z' k), n, vars, ints, outs)      -- trap-escape
  | k == 0    = (Nop z, n, vars, ints, outs)
  | otherwise = (Escape z' (k-1), n, vars, ints, outs)
step (Trap z p, n, vars, ints, outs)                -- trap-adv
  = stepAdv (p, n, vars, ints, outs) (\p' -> Trap z p')

step (Error _ msg, _, _, _, _) = error ("Runtime error: " ++ msg)

step (p, n, vars, ints, outs)                    -- pop
  | isReducible (p,n,vars,ints, outs) = (p, n-1, vars, ints, outs)

step _ = error "step: cannot advance"
--step p =  traceShow p (error "step: cannot advance")

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isReducible :: Desc ann -> Bool
isReducible desc = case desc of
  (_,       n, _, _, _) | n>0 -> True
  (Nop _,   _, _, _, _)       -> False
  (Escape _ _, _, _, _, _)    -> False
  (p,       n, _, _, _)       -> not $ isBlocked n p

-- Awakes all trails waiting for the given event.
-- (pg 8, fig 4.i)
bcast :: ID_Evt -> Vars -> (Stmt ann) -> (Stmt ann)
bcast e vars stmt = case stmt of
  Var z vv p              -> Var z vv (bcast e (vv:vars) p)
  Int z id p              -> Int z id (bcast e vars p)
  AwaitExt z e' | e == e' -> Nop z
  AwaitInt z e' | e == e' -> Nop z
  Every z e' p  | e == e' -> Seq z p (Every z e' p)
  Seq z p q               -> Seq z (bcast e vars p) q
  Trap z p                -> Trap z (bcast e vars p)
  Loop' z p q             -> Loop' z (bcast e vars p) q
  Par' z p q              -> Par' z (bcast e vars p) (bcast e vars q)
  Pause z var p           -> Pause z var (if (varsEval vars (Read z var)) == 1 then p else (bcast e vars p))
  _                     -> stmt -- nothing to do

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single external event.
-- (pg 6)
reaction :: (Stmt ann) -> ID_Ext -> (Stmt ann, Outs)
reaction p ext = (p',outs') where (p',_,_,_,outs') = steps (bcast ext [] p, 0, [], [], [])

steps :: Desc ann -> Desc ann
steps d
  | not $ isReducible d = d
  | otherwise = steps $ step d
  -- | otherwise = traceShow d (steps $ step d)

type Result = Either Errors (Val,[Outs])

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
run :: (G.Stmt ann) -> [a] -> (Stmt ann -> a -> (Stmt ann, Outs)) -> Result
run prog ins reaction = eP (fromGrammar prog) ins []
  where
    --eP :: Stmt -> [a] -> [Outs] -> (Val,[Outs])
    eP prog ins outss = case prog of
      (Var _ ("_ret",val) (AwaitExt _ "FOREVER"))
        | not (null ins) -> Left ["pending inputs"]
        | isNothing val  -> Left ["no return value"]
        | otherwise      -> Right ((fromJust val), outss)
      _
        | null ins       -> Left ["program didn't terminate"]
        | otherwise      -> eP prog' (tail ins) (outss++[outs']) where
                               (prog',outs') = reaction prog (head ins)

-- Evaluates program over history of input events.
-- Returns the last value of global "_ret" set by the program.
compile_run :: Eq ann => (G.Stmt ann) -> [ID_Ext] -> Result
compile_run prog ins =
  let (es,p) = Check.compile (True,True) prog in
    if es == [] then
      run p ("BOOT":ins) reaction
    else
      Left es
