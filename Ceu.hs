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
type Envs = [Env]

newEnv :: Env
newEnv = ([], [])

envsDcl :: Envs -> String -> Envs                -- adds uninitialized variable
envsDcl (env:envs) id = (id: (fst env), snd env) : envs

envsGet :: Envs -> String -> (Maybe (Envs,Env,Envs))         -- gets Env of given variable
envsGet envs id = envsGet' [] envs id where
  envsGet' :: Envs -> Envs -> String -> (Maybe (Envs,Env,Envs))
  envsGet' _ [] _ = Nothing
  envsGet' envsNo (env:envsMaybe) id =
    let has = elem id (fst env) in
      case has of
        True -> Just (envsNo,env,envsMaybe)
        False -> (envsGet' ([env]++envs) envsMaybe id)

envsWrite :: Envs -> String -> Val -> (Maybe Envs)   -- may fail if not declared
envsWrite envs id val =
  let envs' = (envsGet envs id) in
    case envs' of
      Nothing -> Nothing
      Just (envs1,env,envs2) -> Just (envs1 ++ [(fst env, (id,val):(snd env))] ++ envs2)

envsRead :: Envs -> String -> (Maybe Val)
envsRead envs id =
  let env = (envsGet envs id) in
    case env of
      Nothing -> Nothing
      Just (_, (_,hst), _) -> (envsRead hst id) where
        envsRead [] id = Nothing
        envsRead ((id',val'):hst') id = if id==id' then (Just val') else (envsRead hst' id)

-- Expressions.

data Exp
  = Const Val
  | Read ID
  | Umn Exp
  | Add Exp Exp
  | Sub Exp Exp
  deriving (Eq,Show)

evalExp1 :: Envs -> Exp -> (Val->Val) -> (Maybe Val)
evalExp1 envs e op =
  let v = (evalExp envs e) in
    case v of
      Nothing -> Nothing
      (Just v') -> Just (op v')

evalExp2 :: Envs -> Exp -> Exp -> (Val->Val->Val) -> (Maybe Val)
evalExp2 envs e1 e2 op =
  let v1 = (evalExp envs e1)
      v2 = (evalExp envs e2) in
    case v1 of
      Nothing -> Nothing
      (Just v1') ->
        case v2 of
          Nothing -> Nothing
          (Just v2') -> Just (op v1' v2')

evalExp :: Envs -> Exp -> (Maybe Val)
evalExp envs e =
  case e of
    Const val -> (Just val)
    Read id -> envsRead envs id
    Umn e -> evalExp1 envs e negate
    Add e1 e2 -> evalExp2 envs e1 e2 (+)
    Sub e1 e2 -> evalExp2 envs e1 e2 (-)

-- Program.
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
  | Envs' Envs                  -- reset environment
  | Nop
  deriving (Eq,Show)

-- Description.
type Desc = (Stmt, Lvl, Maybe Evt, Envs)

desc1 :: Desc -> Stmt
desc1 (p, n, e, envs) = p
desc2 :: Desc -> Lvl
desc2 (p, n, e, envs) = n
desc3 :: Desc -> Maybe Evt
desc3 (p, n, e, envs) = e
desc4 :: Desc -> Envs
desc4 (p, n, e, envs) = envs


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
        otherwise -> let (p, n, e, envs) = (fromJust res) in
                       Just (f p, n, e, envs)

-- Single nested transition.
nst1 :: Desc -> Maybe Desc

nst1 (Block p, n, Nothing, envs)      -- block-expd
  = Just (Seq p (Envs' envs), n, Nothing, (newEnv : envs))

nst1 (Envs' envs', n, Nothing, envs)  -- envs'
  = Just (Nop, n, Nothing, envs')

nst1 (Var id, n, Nothing, envs)       -- var
  = Just (Nop, n, Nothing, (envsDcl envs id))

nst1 (Write id exp, n, Nothing, envs) -- write
  = let v = (evalExp envs exp) in
      case v of
        Nothing -> Nothing
        (Just v') ->
          let envs' = (envsWrite envs id v') in
            case envs' of
              Nothing -> Nothing
              (Just envs'') -> Just (Nop, n, Nothing, envs'')

nst1 (EmitInt e, n, Nothing, envs)    -- emit-int
  = Just (CanRun n, n, Just e, envs)

nst1 (CanRun m, n, Nothing, envs)     -- can-run
  | m == n = Just (Nop, n, Nothing, envs)
  | otherwise = Nothing

nst1 (Seq Nop q, n, Nothing, envs)    -- seq-nop
  = Just (q, n, Nothing, envs)

nst1 (Seq Break q, n, Nothing, envs)  -- seq-brk
  = Just (Break, n, Nothing, envs)

nst1 (Seq p q, n, Nothing, envs)      -- seq-adv
  = nst1Adv (p, n, Nothing, envs) (\p' -> Seq p' q)

nst1 (If exp p q, n, Nothing, envs)   -- if-true/false
  = let v = (evalExp envs exp) in
      case v of
        Nothing -> Nothing
        (Just v') -> if v' /= 0 then Just (p, n, Nothing, envs)
                                else Just (q, n, Nothing, envs)

nst1 (Loop p, n, Nothing, envs)       -- loop-expd
  = Just (Seq (Loop' p p) (Envs' envs), n, Nothing, envs)

nst1 (Loop' Nop q, n, Nothing, envs)  -- loop-nop
  = Just (Loop q, n, Nothing, envs)

nst1 (Loop' Break q, n, Nothing, envs) -- loop-brk
  = Just (Nop, n, Nothing, envs)

nst1 (Loop' p q, n, Nothing, envs)    -- loop-adv
  = nst1Adv (p, n, Nothing, envs) (\p' -> Loop' p' q)

nst1 (And p q, n, Nothing, envs)      -- and-expd
  = Just (And' p (Seq (CanRun n) q), n, Nothing, envs)

nst1 (And' Nop q, n, Nothing, envs)   -- and-nop1
  = Just (q, n, Nothing, envs)

nst1 (And' Break q, n, Nothing, envs) -- and brk1
  = Just (Seq (clear q) Break, n, Nothing, envs)

nst1 (And' p Nop, n, Nothing, envs)   -- and-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Nop)
  | otherwise = Just (p, n, Nothing, envs)

nst1 (And' p Break, n, Nothing, envs) -- and-brk2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing, envs)

nst1 (And' p q, n, Nothing, envs)     -- and-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> And' p' q)
  | otherwise = nst1Adv (q, n, Nothing, envs) (\q' -> And' p q')

nst1 (Or p q, n, Nothing, envs)       -- or-expd
  = Just (Seq (Or' p (Seq (CanRun n) q)) (Envs' envs), n, Nothing, envs)

nst1 (Or' Nop q, n, Nothing, envs)    -- or-nop1
  = Just (clear q, n, Nothing, envs)

nst1 (Or' Break q, n, Nothing, envs)  -- or-brk1
  = Just (Seq (clear q) Break, n, Nothing, envs)

nst1 (Or' p Nop, n, Nothing, envs)    -- or-nop2
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Nop)
  | otherwise = Just (clear p, n, Nothing, envs)

nst1 (Or' p Break, n, Nothing, envs)
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' Break)
  | otherwise = Just (Seq (clear p) Break, n, Nothing, envs)

nst1 (Or' p q, n, Nothing, envs)      -- or-adv
  | not (isBlocked n p) = nst1Adv (p, n, Nothing, envs) (\p' -> Or' p' q)
  | otherwise = nst1Adv (q, n, Nothing, envs) (\q' -> Or' p q')

nst1 (p, n, e, envs) = Nothing        -- default: none of the previous

-- Zero or more nested transitions.
nst :: Desc -> Desc
nst d
  | isNothing d' = d
  | otherwise = nst (fromJust d')
  where d' = nst1 d

-- Tests whether the description is nst-irreducible.
-- CHECK: nst should only produce nst-irreducible descriptions.
isNstIrreducible :: Desc -> Bool
isNstIrreducible (Nop, n, e, envs) = True
isNstIrreducible (Break, n, e, envs) = True
isNstIrreducible (p, n, Just e, envs) = True
isNstIrreducible (p, n, Nothing, envs) = isBlocked n p


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
out1 (p, n, Just e, envs) = Just (bcast e p, n+1, Nothing, envs)
out1 (p, n, Nothing, envs)
  | n > 0 && isNstIrreducible (p, n, Nothing, envs) = Just (p, n - 1, Nothing, envs)
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
eval2 (p, n, e, envs)
  | isJust e' = eval2 (bcast (fromJust e') p', n+1, Nothing, envs)
  | n' > 0 = eval2 (p', n'-1, Nothing, envs)
  | otherwise = (p', n', e', envs')
  where (p', n', e', envs') = nst (p, n, e, envs)

evalProg :: Stmt -> (Maybe Val)
evalProg prog = envsRead envs "ret" where
  (_,_,_,envs) = eval2 (prog, 0, Nothing, [newEnv])
