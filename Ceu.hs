module Ceu where
import Data.Maybe

-- Event.
type Evt = Int

-- Stack level.
type Lvl = Int

-- Variable / Value.
type ID = String
type Val = Int

-- Environment: pair with a list of declarations and history of all assignments

type Env = ([ID], [(ID,Val)])

envDcl :: Env -> String -> Env                  -- adds uninitialized variable
envDcl env id = (id: (fst env), snd env)

envHas :: Env -> String -> Bool                 -- checks if variable is declared
envHas env id =
  envHas' (fst env) id where
    envHas' [] id = False
    envHas' (id':ids') id = if id'==id then True else envHas' ids' id

envSet :: Env -> String -> Val -> (Maybe Env)   -- may fail if not declared
envSet env id val =
  if (envHas env id) then Just (fst env, (id,val):(snd env))
                     else Nothing

envGet :: Env -> String -> (Maybe Val)
envGet env id =
    envGet' (snd env) id where
      envGet' [] id = Nothing
      envGet' ((id',val'):his') id = if id==id' then (Just val') else (envGet' his' id)

-- Expressions.

data Exp
  = Const Val
  | Read ID
  | Umn Exp
  | Add Exp Exp
  | Sub Exp Exp
  deriving (Eq,Show)

evalExp1 :: Env -> Exp -> (Val->Val) -> (Maybe Val)
evalExp1 env e op =
  let v = (evalExp env e) in
    case v of
      Nothing -> Nothing
      (Just v') -> Just (op v')

evalExp2 :: Env -> Exp -> Exp -> (Val->Val->Val) -> (Maybe Val)
evalExp2 env e1 e2 op =
  let v1 = (evalExp env e1)
      v2 = (evalExp env e2) in
    case v1 of
      Nothing -> Nothing
      (Just v1') ->
        case v2 of
          Nothing -> Nothing
          (Just v2') -> Just (op v1' v2')

evalExp :: Env -> Exp -> (Maybe Val)
evalExp env e =
  case e of
    Const val -> (Just val)
    Read id -> envGet env id
    Umn e -> evalExp1 env e negate
    Add e1 e2 -> evalExp2 env e1 e2 (+)
    Sub e1 e2 -> evalExp2 env e1 e2 (-)

-- Program.
data Stmt
  = Var ID
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
  | Nop
  deriving (Eq,Show)

-- Description.
type Desc = (Stmt, Lvl, Maybe Evt, Env)
desc1 :: Desc -> Stmt
desc1 (p, n, e, env) = p
desc2 :: Desc -> Lvl
desc2 (p, n, e, env) = n
desc3 :: Desc -> Maybe Evt
desc3 (p, n, e, env) = e
desc4 :: Desc -> Env
desc4 (p, n, e, env) = env


----------------------------------------------------------------------------
-- Expressions


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
      case res of
        Nothing -> Nothing
        otherwise -> let d' = (fromJust res) in
                       Just (f (desc1 d'), desc2 d', desc3 d', desc4 d')

-- Single nested transition.
nst1 :: Desc -> Maybe Desc

nst1 (Var id, n, Nothing, env) -- var
  = Just (Nop, n, Nothing, (envDcl env id))

nst1 (Write id exp, n, Nothing, env) -- write
  = let v = (evalExp env exp) in
      case v of
        Nothing -> Nothing
        (Just v') ->
          let env' = (envSet env id v') in
            case env' of
              Nothing -> Nothing
              (Just env'') -> Just (Nop, n, Nothing, env'')

nst1 (EmitInt e, n, Nothing, env)    -- emit-int
  = Just (CanRun n, n, Just e, env)

nst1 (CanRun m, n, Nothing, env)     -- can-run
  | m == n = Just (Nop, n, Nothing, env)
  | otherwise = Nothing

nst1 (Seq Nop q, n, Nothing, env)    -- seq-nop
  = Just (q, n, Nothing, env)

nst1 (Seq Break q, n, Nothing, env)  -- seq-brk
  = Just (Break, n, Nothing, env)

nst1 (Seq p q, n, Nothing, env)      -- seq-adv
  = nst1Adv (p, n, Nothing, env) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, env)
  = let v = (evalExp env exp) in
      case v of
        Nothing -> Nothing
        (Just v') -> if v' /= 0 then Just (p, n, Nothing, env)
                                else Just (q, n, Nothing, env)

nst1 (Loop p, n, Nothing, env)       -- loop-expd
  = Just (Loop' p p, n, Nothing, env)

nst1 (Loop' Nop q, n, Nothing, env)  -- loop-nop
  = Just (Loop q, n, Nothing, env)

nst1 (Loop' Break q, n, Nothing, env) -- loop-brk
  = Just (Nop, n, Nothing, env)

nst1 (Loop' p q, n, Nothing, env)    -- loop-adv
  = nst1Adv (p, n, Nothing, env) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, env)      -- and-expd
  = Just (And' p (Seq (CanRun n) q), n, Nothing, env)

nst1 (And' Nop q, n, Nothing, env)   -- and-nop1
  = Just (q, n, Nothing, env)

nst1 (And' Break q, n, Nothing, env) -- and brk1
  = Just (Seq (clear q) Break, n, Nothing, env)

nst1 (And' p Nop, n, Nothing, env)   -- and-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> And' p' Nop)
  | otherwise = Just (p, n, Nothing, env)

nst1 (And' p Break, n, Nothing, env) -- and-brk2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> And' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing, env)

nst1 (And' p q, n, Nothing, env)     -- and-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> And' p' q)
  | otherwise = nst1Adv (q, n, Nothing, env) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, env)       -- or-expd
  = Just (Or' p (Seq (CanRun n) q), n, Nothing, env)

nst1 (Or' Nop q, n, Nothing, env)    -- or-nop1
  = Just (clear q, n, Nothing, env)

nst1 (Or' Break q, n, Nothing, env)  -- or-brk1
  = Just (Seq (clear q) Break, n, Nothing, env)

nst1 (Or' p Nop, n, Nothing, env)    -- or-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' Nop)
  | otherwise = Just (clear p, n, Nothing, env)

nst1 (Or' p Break, n, Nothing, env)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing, env)

nst1 (Or' p q, n, Nothing, env)      -- or-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, env) (\p' -> Or' p' q)
  | otherwise = nst1Adv (q, n, Nothing, env) (\q' -> Or' p q')

nst1 (p, n, e, env) = Nothing        -- default: none of the previous

-- Zero or more nested transitions.
nst :: Desc -> Desc
nst d
  | isNothing d' = d
  | otherwise = nst (fromJust d')
  where d' = nst1 d

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible (Nop, n, e, env) = True
isNstIrreducible (Break, n, e, env) = True
isNstIrreducible (p, n, Just e, env) = True
isNstIrreducible (p, n, Nothing, env) = isBlocked n p


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
out1 (p, n, Just e, env) = Just (bcast e p, n+1, Nothing, env)
out1 (p, n, Nothing, env)
  | n > 0 && isNstIrreducible (p, n, Nothing, env) = Just (p, n - 1, Nothing, env)
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
eval2 (p, n, e, env)
  | isJust e' = eval2 (bcast (fromJust e') p', n+1, Nothing, env)
  | n' > 0 = eval2 (p', n'-1, Nothing, env)
  | otherwise = (p', n', e', env')
  where (p', n', e', env') = nst (p, n, e, env)
