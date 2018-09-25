module Ceu where
import Data.Maybe

-- Event.
type Evt = Int

-- Stack level.
type Lvl = Int

-- Program.
-- TODO: Add variables and conditionals.
data Stmt
  = AwaitExt Evt
  | AwaitInt Evt
  | EmitInt Evt
  | Break
  | Seq Stmt Stmt
  | Loop Stmt
  | Every Evt Stmt
  | And Stmt Stmt
  | Or Stmt Stmt
  | Fin Stmt
  | Loop' Stmt Stmt             -- unrolled Loop
  | And' Stmt Stmt              -- unrolled And
  | Or' Stmt Stmt               -- unrolled Or
  | CanRun Lvl
  | Nop
  deriving (Eq,Show)

-- Description.
type Desc = (Stmt, Lvl, Maybe Evt)
desc1 :: Desc -> Stmt
desc1 (p, n, e) = p
desc2 :: Desc -> Lvl
desc2 (p, n, e) = n
desc3 :: Desc -> Maybe Evt
desc3 (p, n, e) = e


----------------------------------------------------------------------------
-- Nested transition

-- Tests whether program is blocked at the given stack level.
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
isBlocked n p = False           -- otherwise

-- Obtains the body of all active Fin statements in program.
clear :: Stmt -> Stmt
clear p = if isJust p' then fromJust p' else Nop
  where p' = clear' p

clear' :: Stmt -> Maybe Stmt
clear' (AwaitExt e) = Nothing
clear' (AwaitInt e) = Nothing
clear' (Every e p) = Nothing
clear' (CanRun n) = Nothing
clear' (Fin p) = Just p
clear' (Seq p q) = clear' p
clear' (Loop' p q) = clear' p
clear' (And' p q)
  | isNothing p' = q'
  | isNothing q' = p'
  | otherwise = Just (Seq (fromJust p') (fromJust q'))
  where p' = clear' p; q' = clear' q
clear' (Or' p q)
  | isNothing p' = q'
  | isNothing q' = p'
  | otherwise = Just (Seq (fromJust p') (fromJust q'))
  where p' = clear' p; q' = clear' q
clear' p = Nothing              -- otherwise

-- Helper function used by nst1 in the *-adv rules.
nst1Adv :: Desc -> (Stmt -> Stmt) -> Maybe Desc
nst1Adv d f
  = let res = (nst1 d) in
      if res == Nothing then Nothing
      else let d' = (fromJust res) in
             Just (f (desc1 d'), desc2 d', desc3 d')

-- Single nested transition.
nst1 :: Desc -> Maybe Desc

nst1 (EmitInt e, n, Nothing)    -- emit-int
  = Just (CanRun n, n, Just e)

nst1 (CanRun m, n, Nothing)     -- can-run
  | m == n = Just (Nop, n, Nothing)
  | otherwise = Nothing

nst1 (Seq Nop q, n, Nothing)    -- seq-nop
  = Just (q, n, Nothing)

nst1 (Seq Break q, n, Nothing)  -- seq-brk
  = Just (Break, n, Nothing)

nst1 (Seq p q, n, Nothing)      -- seq-adv
  = nst1Adv (p, n, Nothing) (\p' -> Seq p' q)

nst1 (Loop p, n, Nothing)       -- loop-expd
  = Just (Loop' p p, n, Nothing)

nst1 (Loop' Nop q, n, Nothing)  -- loop-nop
  = Just (Loop q, n, Nothing)

nst1 (Loop' Break q, n, Nothing) -- loop-brk
  = Just (Nop, n, Nothing)

nst1 (Loop' p q, n, Nothing)    -- loop-adv
  = nst1Adv (p, n, Nothing) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing)      -- and-expd
  = Just (And' p (Seq (CanRun n) q), n, Nothing)

nst1 (And' Nop q, n, Nothing)   -- and-nop1
  = Just (q, n, Nothing)

nst1 (And' Break q, n, Nothing) -- and brk1
  = Just (Seq (clear q) Break, n, Nothing)

nst1 (And' p Nop, n, Nothing)   -- and-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> And' p' Nop)
  | otherwise = Just (p, n, Nothing)

nst1 (And' p Break, n, Nothing) -- and-brk2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> And' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing)

nst1 (And' p q, n, Nothing)     -- and-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> And' p' q)
  | otherwise = nst1Adv (q, n, Nothing) (\q' -> And' p q')

nst1 (Or p q, n, Nothing)       -- or-expd
  = Just (Or' p (Seq (CanRun n) q), n, Nothing)

nst1 (Or' Nop q, n, Nothing)    -- or-nop1
  = Just (clear q, n, Nothing)

nst1 (Or' Break q, n, Nothing)  -- or-brk1
  = Just (Seq (clear q) Break, n, Nothing)

nst1 (Or' p Nop, n, Nothing)    -- or-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> Or' p' Nop)
  | otherwise = Just (clear p, n, Nothing)

nst1 (Or' p Break, n, Nothing)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> Or' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing)

nst1 (Or' p q, n, Nothing)      -- or-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing) (\p' -> Or' p' q)
  | otherwise = nst1Adv (q, n, Nothing) (\q' -> Or' p q')

nst1 (p, n, e) = Nothing        -- default: none of the previous

-- Zero or more nested transitions.
nst :: Desc -> Desc
nst d
  | isNothing d' = d
  | otherwise = nst (fromJust d')
  where d' = nst1 d

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible (Nop, n, e) = True
isNstIrreducible (Break, n, e) = True
isNstIrreducible (p, n, Just e) = True
isNstIrreducible (p, n, Nothing) = isBlocked n p


----------------------------------------------------------------------------
-- Outermost transition

-- Awakes all trails waiting for the given event.
bcast :: Evt -> Stmt -> Stmt
bcast e (AwaitExt e') = if e == e' then Nop else AwaitExt e'
bcast e (AwaitInt e') = if e == e' then Nop else AwaitInt e'
bcast e (Every e' p) = if e == e' then (Seq p (Every e' p)) else (Every e' p)
bcast e (Seq p q) = Seq (bcast e p) q
bcast e (Loop' p q) = Loop' (bcast e p) q
bcast e (And' p q) = And' (bcast e p) (bcast e q)
bcast e (Or' p q) = Or' (bcast e p) (bcast e q)
bcast e p = p -- otherwise

-- Single outermost transition.
out1 :: Desc -> Maybe Desc
out1 (p, n, Just e) = Just (bcast e p, n+1, Nothing)
out1 (p, n, Nothing)
  | n > 0 && isNstIrreducible (p, n, Nothing) = Just (p, n - 1, Nothing)
  | otherwise = Nothing

-- Zero or more outermost transitions.
out :: Desc -> Desc
out d
  | isNothing d' = d
  | otherwise = out (fromJust d')
  where d' = out1 d

-- TODO: Define pot.
-- TODO: Define rank.


----------------------------------------------------------------------------
-- Eval

-- TODO: Define eval1 as in the paper (via nst+out+rank).
-- eval1 :: Desc -> Desc

-- Alternative (more direct) definition of eval1.
-- CHECK: eval1/2 should only produce (nst+out)-irreducible descriptions.
-- CHECK: eval1/2 should be equivalent.
eval2 :: Desc -> Desc
eval2 (p, n, e)
  | isJust e' = eval2 (bcast (fromJust e') p', n+1, Nothing)
  | n' > 0 = eval2 (p', n'-1, Nothing)
  | otherwise = (p', n', e')
  where (p', n', e') = nst (p, n, e)
