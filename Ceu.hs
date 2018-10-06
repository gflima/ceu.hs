module Ceu where

import Data.Maybe

-- Event.
type Evt = Int

-- Stack level.
type Lvl = Int

-- Variable / Value.
type ID = String
type Val = Int

-- Environment (declarations plus assignment history).
type Env = ([ID], [(ID,Val)])
type Envs = [Env]

-- Expression.
data Exp
  = Const Val
  | Read ID
  | Umn Exp
  | Add Exp Exp
  | Sub Exp Exp
  deriving (Eq, Show)

-- Program (pg 5).
data Stmt
  = Block Stmt
  | Var ID
  | Write ID Exp
  | AwaitExt Evt
  | AwaitInt Evt
  | EmitInt Evt
  | Break
  | Seq Stmt Stmt
  | If Exp Stmt Stmt
  | Loop Stmt
  | Every Evt Stmt
  | And Stmt Stmt
  | Or Stmt Stmt
  | Fin Stmt
  | Loop' Stmt Stmt             -- unrolled Loop
  | And' Stmt Stmt              -- unrolled And
  | Or' Stmt Stmt               -- unrolled Or
  | CanRun Lvl
  | Envs' Int                   -- reset environment
  | Nop
  deriving (Eq, Show)

-- Description (pg 6).
type Desc = (Stmt, Lvl, Maybe Evt, Envs)

----------------------------------------------------------------------------
-- Environment

-- The empty environment.
newEnv :: Env
newEnv = ([], [])

-- Adds uninitialized variable to environment.
-- CHECK: Envs must be nonempty.
envsDcl :: Envs -> String -> Envs
envsDcl [] _ = error "envsDcl: bad environment"
envsDcl (env:envs) id = (id : (fst env), snd env) : envs

-- Finds the first environment containing the given variable.
envsGet :: Envs -> String -> (Envs,Env,Envs)
envsGet [] _ = error "envsGet: bad environment"
envsGet envs id  = envsGet' [] envs id where
  envsGet' :: Envs -> Envs -> String -> (Envs,Env,Envs)
  envsGet' _ [] _ = error "envsGet: undeclared variable"
  envsGet' envsNotHere (env:envsMaybeHere) id
    | elem id (fst env) = (envsNotHere,env,envsMaybeHere) -- found
    | otherwise = (envsGet' (envsNotHere ++ [env]) envsMaybeHere id)

-- Writes value to variable in environment.
envsWrite :: Envs -> String -> Val -> Envs
envsWrite envs id val = (envs1 ++ [(fst env, (id,val):(snd env))] ++ envs2)
  where (envs1,env,envs2) = (envsGet envs id)

-- Reads variable value from environment.
envsRead :: Envs -> String -> Val
envsRead envs id =
  let (_, (_,hst), _) = (envsGet envs id) in
      (envsRead' hst id) where
        envsRead' [] id = error "envsRead: uninitialized variable"
        envsRead' ((id',val'):hst') id
          = if id==id' then val' else (envsRead' hst' id)

----------------------------------------------------------------------------
-- Expression

-- Evaluates unary operator.
evalExp1 :: Envs -> Exp -> (Val->Val) -> Val
evalExp1 envs e op = op (evalExp envs e)

-- Evaluates binary operator.
evalExp2 :: Envs -> Exp -> Exp -> (Val->Val->Val) -> Val
evalExp2 envs e1 e2 op =
  let v1 = (evalExp envs e1)
      v2 = (evalExp envs e2) in
           (op v1 v2)

-- Evaluates expression in environment.
evalExp :: Envs -> Exp -> Val
evalExp envs e =
  case e of
    Const val -> val
    Read id -> envsRead envs id
    Umn e -> evalExp1 envs e negate
    Add e1 e2 -> evalExp2 envs e1 e2 (+)
    Sub e1 e2 -> evalExp2 envs e1 e2 (-)

----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
-- (pg 8, fig 4.ii)
isBlocked :: Lvl -> Stmt -> Bool
isBlocked n (AwaitExt e) = True
isBlocked n (AwaitInt e) = True
isBlocked n (Every e p) = True
isBlocked n (CanRun m) = n > m
isBlocked n (Fin p) = True
isBlocked n (Seq p q) = isBlocked n p
isBlocked n (Loop' p q) = isBlocked n p
isBlocked n (And' p q) = (isBlocked n p) && (isBlocked n q)
isBlocked n (Or' p q) = (isBlocked n p) && (isBlocked n q)
isBlocked _ _ = False           -- otherwise

-- Obtains the body of all active Fin statements in program.
-- (pg 8, fig 4.iii)
clear :: Stmt -> Stmt
clear (AwaitExt _) = Nop
clear (AwaitInt _) = Nop
clear (Every _ _) = Nop
clear (CanRun _) = Nop
clear (Fin p) = p
clear (Seq p _) = clear p
clear (Loop' p _) = clear p
clear (And' p q) = (Seq (clear p) (clear q))
clear (Or' p q) = (Seq (clear p) (clear q))
clear _ = error "clear: invalid clear"

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Desc
nst1Adv d f = (f p, n, e, envs) where
  (p, n, e, envs) = (nst1 d)

-- Single nested transition.
-- (pg 6)
nst1 :: Desc -> Desc

nst1 (Block p, n, Nothing, envs)                -- block-expd
  = (Seq p (Envs' (length envs)), n, Nothing, (newEnv : envs))

nst1 (Envs' lvl, n, Nothing, envs)              -- envs'
  = (Nop, n, Nothing, drop ((length envs)-lvl) envs)

nst1 (Var id, n, Nothing, envs)                 -- var
  = (Nop, n, Nothing, (envsDcl envs id))

nst1 (Write id exp, n, Nothing, envs)           -- write
  = (Nop, n, Nothing, (envsWrite envs id (evalExp envs exp)))

nst1 (EmitInt e, n, Nothing, envs)              -- emit-int (pg 6)
  = (CanRun n, n, Just e, envs)

nst1 (CanRun m, n, Nothing, envs)     -- can-run (pg 6)
  | m == n = (Nop, n, Nothing, envs)
  | otherwise = error "nst1: cannot advance"

nst1 (Seq Nop q, n, Nothing, envs)    -- seq-nop (pg 6)
  = (q, n, Nothing, envs)

nst1 (Seq Break q, n, Nothing, envs)  -- seq-brk (pg 6)
  = (Break, n, Nothing, envs)

nst1 (Seq p q, n, Nothing, envs)      -- seq-adv (pg 6)
  = nst1Adv (p, n, Nothing, envs) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, envs)   -- if-true/false (pg 6)
  | v /= 0 = (p, n, Nothing, envs)
  | otherwise = (q, n, Nothing, envs)
  where v = (evalExp envs exp)

nst1 (Loop p, n, Nothing, envs)       -- loop-expd (pg 7)
  = (Seq (Loop' p p) (Envs' (length envs)), n, Nothing, envs)

nst1 (Loop' Nop q, n, Nothing, envs)  -- loop-nop (pg 7)
  = (Loop q, n, Nothing, envs)

nst1 (Loop' Break q, n, Nothing, envs) -- loop-brk (pg 7)
  = (Nop, n, Nothing, envs)

nst1 (Loop' p q, n, Nothing, envs)    -- loop-adv (pg 7)
  = nst1Adv (p, n, Nothing, envs) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, envs)      -- and-expd (pg 7)
  = (And' p (Seq (CanRun n) q), n, Nothing, envs)

nst1 (And' Nop q, n, Nothing, envs)   -- and-nop1 (pg 7)
  = (q, n, Nothing, envs)

nst1 (And' Break q, n, Nothing, envs) -- and brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, envs)

nst1 (And' p Nop, n, Nothing, envs)   -- and-nop2 (pg 7)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Nop)
  | otherwise = (p, n, Nothing, envs)

nst1 (And' p Break, n, Nothing, envs) -- and-brk2 (pg 7)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Break)
  | otherwise = (Seq (clear p) Break, n, Nothing, envs)

nst1 (And' p q, n, Nothing, envs)     -- and-adv (pg 7)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' q)
  | otherwise = nst1Adv (q, n, Nothing, envs) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, envs)       -- or-expd (pg 7)
  = (Seq (Or' p (Seq (CanRun n) q)) (Envs' (length envs)), n, Nothing, envs)

nst1 (Or' Nop q, n, Nothing, envs)    -- or-nop1 (pg 7)
  = (clear q, n, Nothing, envs)

nst1 (Or' Break q, n, Nothing, envs)  -- or-brk1 (pg 7)
  = (Seq (clear q) Break, n, Nothing, envs)

nst1 (Or' p Nop, n, Nothing, envs)    -- or-nop2 (pg 7)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Nop)
  | otherwise = (clear p, n, Nothing, envs)

nst1 (Or' p Break, n, Nothing, envs)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Break)
  | otherwise = (Seq (clear p) Break, n, Nothing, envs)

nst1 (Or' p q, n, Nothing, envs)      -- or-adv (pg 7)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' q)
  | otherwise = nst1Adv (q, n, Nothing, envs) (\q' -> Or' p q')

nst1 (_, _, _, _) = error "nst1: cannot advance"

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible (Nop, n, e, envs) = True
isNstIrreducible (Break, n, e, envs) = True
isNstIrreducible (p, n, Just e, envs) = True
isNstIrreducible (p, n, Nothing, envs) = isBlocked n p

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
bcast e (AwaitExt e') = if e == e' then Nop else AwaitExt e'
bcast e (AwaitInt e') = if e == e' then Nop else AwaitInt e'
bcast e (Every e' p) = if e == e' then (Seq p (Every e' p)) else (Every e' p)
bcast e (Seq p q) = Seq (bcast e p) q
bcast e (Loop' p q) = Loop' (bcast e p) q
bcast e (And' p q) = And' (bcast e p) (bcast e q)
bcast e (Or' p q) = Or' (bcast e p) (bcast e q)
bcast e p = p -- otherwise

-- (pg 6)
outPush :: Desc -> Desc
outPush (_, _, Nothing, _)   = error "outPush: missing event"
outPush (p, n, Just e, envs) = (bcast e p, n+1, Nothing, envs)

-- (pg 6)
outPop :: Desc -> Desc
outPop (p, n, Nothing, envs)
  | n>0 && isNstIrreducible (p,n,Nothing,envs) = (p, n-1, Nothing, envs)
  | otherwise = error "outPop: cannot advance"

-- Single outermost transition.
-- (pg 6)
out1 :: Desc -> Desc
out1 (p, n, Just e, envs)  = outPush (p, n, Just e, envs)
out1 (p, n, Nothing, envs) = outPop (p, n, Nothing, envs)

-- (pg 6)
nsts_out1_s :: Desc -> Desc
nsts_out1_s (p,n,e,envs)
  | n==0 = (p,n,e,envs)
  | n>0 = nsts_out1_s (out1 (nsts (p,n,e,envs)))

-- TODO: Define pot.
-- TODO: Define rank.

----------------------------------------------------------------------------
-- Reaction

-- (pg 6)
reaction :: (Stmt,Evt,Envs) -> (Stmt,Envs)
reaction (p,e,envs) = (p',envs') where
  (p',_,_,envs') = nsts_out1_s $ outPush (p,0,(Just e),envs)

evalProg :: Stmt -> Val
evalProg prog = envsRead envs "ret" where
  (_,envs) = reaction (prog,0,[newEnv])
