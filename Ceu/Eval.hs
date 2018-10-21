module Ceu.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Data.Maybe
import Text.Printf
--import Debug.Trace

data Stmt
  = Block Int ([ID_Var],[ID_Evt]) Stmt  -- declaration block
  | Write ID_Var Expr                   -- assignment statement
  | AwaitExt ID_Evt                     -- await external event
  | AwaitInt ID_Evt                     -- await internal event
  | EmitInt ID_Evt                      -- emit internal event
  | Break                               -- loop escape
  | If Int Expr Stmt Stmt               -- conditional
  | Seq Int Stmt Stmt                   -- sequence
  | Loop Int Stmt                       -- infinite loop
  | Every Int ID_Evt Stmt               -- event iteration
  | And Int Stmt Stmt                   -- par/and statement
  | Or Int Stmt Stmt                    -- par/or statement
  | Fin Int Stmt                        -- finalization statement
  | Nop                                 -- dummy statement (internal)
  | Error String                        -- generate runtime error (for testing purposes)
  | CanRun Int                          -- wait for stack level (internal)
  | Restore Int                         -- restore environment (internal)
  | Loop' Int Stmt Stmt                 -- unrolled Loop (internal)
  | And' Int Stmt Stmt                  -- unrolled And (internal)
  | Or' Int Stmt Stmt                   -- unrolled Or (internal)
  deriving (Eq, Show)

fromGrammar :: G.Stmt -> Stmt
fromGrammar p = p' where
    (_,p') = fG 0 p
    fG :: Int -> G.Stmt -> (Int,Stmt)
    fG n (G.Block envs p) = (n',  (Block n envs p'))    where (n',p')   = fG (n+1)   p
    fG n (G.Write id exp) = (n, (Write id exp))
    fG n (G.AwaitExt id)  = (n, (AwaitExt id))
    fG n (G.AwaitInt id)  = (n, (AwaitInt id))
    fG n (G.EmitInt id)   = (n, (EmitInt id))
    fG n G.Break          = (n, Break)
    fG n (G.If exp p1 p2) = (n2', (If n1' exp p1' p2')) where (n1',p1') = fG n       p1
                                                              (n2',p2') = fG (n1'+1) p2
    fG n (G.Seq p1 p2)    = (n2', (Seq n1' p1' p2'))    where (n1',p1') = fG n       p1
                                                              (n2',p2') = fG (n1'+1) p2
    fG n (G.Loop p)       = (n',  (Loop n p'))          where (n',p')   = fG (n+1)   p
    fG n (G.Every id p)   = (n',  (Every n id p'))      where (n',p')   = fG (n+1)   p
    fG n (G.And p1 p2)    = (n2', (And n1' p1' p2'))    where (n1',p1') = fG n       p1
                                                              (n2',p2') = fG (n1'+1) p2
    fG n (G.Or p1 p2)     = (n2', (Or n1' p1' p2'))     where (n1',p1') = fG n       p1
                                                              (n2',p2') = fG (n1'+1) p2
    fG n (G.Fin p)        = (n',  (Fin n p'))           where (n',p')   = fG (n+1)   p
    fG n G.Nop            = (n, Nop)
    fG n (G.Error msg)    = (n, (Error msg))

-- Environment.
type Env = (([ID_Var],[ID_Evt]), [(ID_Var,Val)]) -- declarations plus assignment history
type Envs = [Env]                    -- list of environments

-- Stack level.
type Lvl = Int

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe ID_Evt, Envs)

-- Shows list of declarations (variables or events).
showDcls :: [String] -> String
showDcls dcls = case dcls of
  []     -> ""
  v:[]   -> v
  v:dcls -> v ++ "," ++ showDcls dcls

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Block _ (vs,es) p | null (vs,es) -> printf "{%s}" (sP p)
                    | otherwise    -> printf "{%s/%s: %s}" (sV vs) (sV es) (sP p)
  Write var expr -> printf "%s=%s" var (sE expr)
  AwaitExt e     -> printf "?E%s" e
  AwaitInt e     -> printf "?%s" e
  EmitInt e      -> printf "!%s" e
  Break          -> "break"
  If _ expr p q  -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq _ p q      -> printf "%s; %s" (sP p) (sP q)
  Loop _ p       -> printf "(loop %s)" (sP p)
  Every _ e p    -> printf "(every %s %s)" e (sP p)
  And _ p q      -> printf "(%s && %s)" (sP p) (sP q)
  Or _ p q       -> printf "(%s || %s)" (sP p) (sP q)
  Fin _ p        -> printf "(fin %s)" (sP p)
  Nop            -> "nop"
  Error _        -> "err"
  CanRun n       -> printf "@canrun(%d)" n
  Restore n      -> printf "@restore(%d)" n
  Loop' _ p q    -> printf "(%s @loop %s)" (sP p) (sP q)
  And' _ p q     -> printf "(%s @&& %s)" (sP p) (sP q)
  Or' _ p q      -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExpr
    sP = showProg
    sV = showDcls

----------------------------------------------------------------------------
-- Environment

-- The empty environment.
newEnv :: Env
newEnv = (([],[]), [])

-- Finds the first environment containing the given declaration.
envsGet :: Envs -> String -> (Envs,Env,Envs)
envsGet [] _ = error "envsGet: bad environment"
envsGet envs id  = envsGet' [] envs id
  where
    f = fst
    envsGet' _ [] _  = error ("envsGet: undeclared variable: " ++ id)
    envsGet' notHere (env:maybeHere) id
      | elem id (fst (f env)) = (notHere, env, maybeHere) -- found
      | otherwise             = envsGet' (notHere++[env]) maybeHere id

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
  Mul e1 e2 -> (envsEval envs e1) * (envsEval envs e2)
  Div e1 e2 -> (envsEval envs e1) `div` (envsEval envs e2)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked i stmt = case stmt of
  AwaitExt e  -> True
  AwaitInt e  -> True
  Every _ e p -> True
  CanRun j    -> i > j
  Fin _ p     -> True
  Seq _ p q   -> isBlocked i p
  Loop' _ p q -> isBlocked i p
  And' _ p q  -> isBlocked i p && isBlocked i q
  Or' _ p q   -> isBlocked i p && isBlocked i q
  _           -> False

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear stmt = case stmt of
  AwaitExt _  -> Nop
  AwaitInt _  -> Nop
  Every _ _ _ -> Nop
  CanRun _    -> Nop
  Fin _ p     -> p
  Seq _ p _   -> clear p
  Loop' _ p _ -> clear p
  And' n p q  -> Seq n (clear p) (clear q)
  Or' n p q   -> Seq n (clear p) (clear q)
  _           -> error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Desc
nst1Adv d f = (f p, i, e, envs)
  where
    (p, i, e, envs) = nst1 d

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Block n dcls p, i, Nothing, envs)           -- block
  = (Seq n p (Restore (length envs)), i, Nothing, (dcls,[]):envs)

nst1 (Restore lvl, i, Nothing, envs)            -- restore
  = (Nop, i, Nothing, drop (length envs - lvl) envs)

nst1 (Write id exp, i, Nothing, envs)           -- write
  = (Nop, i, Nothing, envsWrite envs id (envsEval envs exp))

nst1 (EmitInt e, i, Nothing, envs)              -- emit-int (pg 6)
  = (CanRun i, i, Just e, envs)

nst1 (CanRun m, i, Nothing, envs)               -- can-run (pg 6)
  | m == i    = (Nop, i, Nothing, envs)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq n Nop q, i, Nothing, envs)              -- seq-nop (pg 6)
  = (q, i, Nothing, envs)

nst1 (Seq n Break q, i, Nothing, envs)            -- seq-brk (pg 6)
  = (Break, i, Nothing, envs)

nst1 (Seq n p q, i, Nothing, envs)                -- seq-adv (pg 6)
  = nst1Adv (p, i, Nothing, envs) (\p' -> Seq n p' q)

nst1 (If n exp p q, i, Nothing, envs)             -- if-true/false (pg 6)
  | envsEval envs exp /= 0 = (p, i, Nothing, envs)
  | otherwise              = (q, i, Nothing, envs)

nst1 (Loop n p, i, Nothing, envs)                 -- loop-expd (pg 7)
  = (Seq n (Loop' n p p) (Restore (length envs)), i, Nothing, envs)

nst1 (Loop' n Nop q, i, Nothing, envs)            -- loop-nop (pg 7)
  = (Loop n q, i, Nothing, envs)

nst1 (Loop' n Break q, i, Nothing, envs)          -- loop-brk (pg 7)
  = (Nop, i, Nothing, envs)

nst1 (Loop' n p q, i, Nothing, envs)              -- loop-adv (pg 7)
  = nst1Adv (p, i, Nothing, envs) (\p' -> Loop' n p' q)

nst1 (And n p q, i, Nothing, envs)                -- and-expd (pg 7)
  = (And' n p (Seq n (CanRun i) q), i, Nothing, envs)

nst1 (And' n Nop q, i, Nothing, envs)             -- and-nop1 (pg 7)
  = (q, i, Nothing, envs)

nst1 (And' n Break q, i, Nothing, envs)           -- and brk1 (pg 7)
  = (Seq n (clear q) Break, i, Nothing, envs)

nst1 (And' n p Nop, i, Nothing, envs)             -- and-nop2 (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> And' n p' Nop)
  | otherwise           = (p, i, Nothing, envs)

nst1 (And' n p Break, i, Nothing, envs)           -- and-brk2 (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> And' n p' Break)
  | otherwise           = (Seq n (clear p) Break, i, Nothing, envs)

nst1 (And' n p q, i, Nothing, envs)               -- and-adv (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> And' n p' q)
  | otherwise           = nst1Adv (q, i, Nothing, envs) (\q' -> And' n p q')

nst1 (Or n p q, i, Nothing, envs)                 -- or-expd (pg 7)
  = (Seq n (Or' n p (Seq n (CanRun i) q)) (Restore (length envs)), i, Nothing, envs)

nst1 (Or' n Nop q, i, Nothing, envs)              -- or-nop1 (pg 7)
  = (clear q, i, Nothing, envs)

nst1 (Or' n Break q, i, Nothing, envs)            -- or-brk1 (pg 7)
  = (Seq n (clear q) Break, i, Nothing, envs)

nst1 (Or' n p Nop, i, Nothing, envs)              -- or-nop2 (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> Or' n p' Nop)
  | otherwise           = (clear p, i, Nothing, envs)

nst1 (Or' n p Break, i, Nothing, envs)            -- or-brk2 (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> Or' n p' Break)
  | otherwise           = (Seq n (clear p) Break, i, Nothing, envs)

nst1 (Or' n p q, i, Nothing, envs)                -- or-adv (pg 7)
  | not $ isBlocked i p = nst1Adv (p, i, Nothing, envs) (\p' -> Or' n p' q)
  | otherwise           = nst1Adv (q, i, Nothing, envs) (\q' -> Or' n p q')

nst1 (Error msg, _, Nothing, _) = error ("Runtime error: " ++ msg)

nst1 (_, _, _, _) = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible desc = case desc of
  (Nop, i, e, envs)     -> True
  (Break, i, e, envs)   -> True
  (p, i, Just e, envs)  -> True
  (p, i, Nothing, envs) -> isBlocked i p

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
bcast :: ID_Evt -> Stmt -> Stmt
bcast e stmt = case stmt of
  AwaitExt e'  | e == e' -> Nop
  AwaitInt e'  | e == e' -> Nop
  Every n e' p | e == e' -> Seq n p (Every n e' p)
  Seq n p q              -> Seq n (bcast e p) q
  Loop' n p q            -> Loop' n (bcast e p) q
  And' n p q             -> And' n (bcast e p) (bcast e q)
  Or' n p q              -> Or' n (bcast e p) (bcast e q)
  _                      -> stmt -- nothing to do

-- (pg 6)
outPush :: Desc -> Desc
outPush (p, i, Just e, envs) = (bcast e p, i+1, Nothing, envs)
outPush (_, _, Nothing, _)   = error "outPush: missing event"

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, i, Nothing, envs)
  | i>0 && isNstIrreducible (p, i, Nothing, envs) = (p, i-1, Nothing, envs)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, i, Just e, envs)  = outPush (p, i, Just e, envs)
out1 (p, i, Nothing, envs) = outPop (p, i, Nothing, envs)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p, i, e, envs)
  | i == 0 = (p, i, e, envs)
  | i > 0  = nsts_out1_s $ out1 $ nsts (p, i, e, envs)

-- Counts the maximum number of EmitInt's that can be executed in program.
-- (pot', pg 9)
countMaxEmits :: Stmt -> Int
countMaxEmits stmt = case stmt of
  EmitInt e            -> 1
  If _ expr p q        -> max (cME p) (cME q)
  Loop _ p             -> cME p
  And _ p q            -> cME p + cME q
  Or _ p q             -> cME p + cME q
  Seq _ Break q        -> 0
  Seq _ (AwaitExt e) q -> 0
  Seq _ p q            -> cME p + cME q
  --Loop' _ p q | checkLoop (Loop _ p) -> cME p         -- q is unreachable
              -- | otherwise            -> cME p + cME q
  Loop' _ p q          -> cME p + cME q -- TODO: is counting 2x a problem?
  And' _ p q           -> cME p + cME q -- CHECK THIS! --
  Or' _ p q            -> cME p + cME q -- CHECK THIS! --
  _                    -> 0
  where
    cME = countMaxEmits

-- Counts the maximum number of EmitInt's that can be executed in a reaction
-- of program to event.
-- (pg 9)
pot :: ID_Evt -> Stmt -> Int
pot e p = countMaxEmits $ bcast e p

-- (pg 9)
rank :: Desc -> (Int, Int)
rank (p, i, Nothing, envs) = (0, i)
rank (p, i, Just e, envs)  = (pot e p, i+1)

-- Tests whether the description is irreducible in general.
isIrreducible :: Desc -> Bool
isIrreducible d = isNstIrreducible d && snd (rank d) == 0

----------------------------------------------------------------------------
-- Reaction

-- Computes a reaction of program plus environment to a single event.
-- (pg 6)
reaction :: (Stmt, ID_Evt, Envs) -> (Stmt, Envs)
reaction (p, e, envs) = (p', envs')
  where
    (p', _, _, envs') = nsts_out1_s $ outPush (p, 0, Just e, envs)

-- Evaluates program over history of input events.
-- Returns the last value of global "ret" set by the program.
evalProg :: G.Stmt -> [ID_Evt] -> Val
evalProg prog hist = evalProg' (fromGrammar (G.Block (["ret"],[]) (G.Seq prog (G.AwaitExt "FOREVER")))) ("FOREVER":hist) []
  where                         -- enclosing block with "ret" that never terminates
    evalProg' :: Stmt -> [ID_Evt] -> Envs -> Val
    evalProg' prog hist envs = case prog of
      (Seq _ (AwaitExt "FOREVER") (Restore 0))
          | null hist -> envsRead envs "ret"  -- done
          | otherwise -> error "evalProg: pending inputs"
      _   | null hist -> error "evalProg: program didn't terminate"
          | otherwise ->                     -- continue
            let (prog', envs') = reaction (prog, head hist, envs) in
              evalProg' prog' (tail hist) envs'
