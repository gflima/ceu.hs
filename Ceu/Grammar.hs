module Ceu.Grammar where

import Ceu.Globals
import Text.Printf

-- Program (pg 5).
data Stmt
  = Var ID_Var Stmt             -- variable declaration
  | Int ID_Int Stmt             -- event declaration
  | Write ID_Var Exp            -- assignment statement
  | AwaitExt ID_Ext             -- await external event
  | EmitExt ID_Ext (Maybe Exp)  -- emit external event
  | AwaitInt ID_Int             -- await internal event
  | EmitInt ID_Int              -- emit internal event
  | Break                       -- loop escape
  | If Exp Stmt Stmt            -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every ID_Evt Stmt           -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Pause ID_Var Stmt           -- pause/suspend statement
  | Fin Stmt                    -- finalization statement
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Var id p             -> printf "{%s: %s}" id (sP p)
  Int id p             -> printf "{%s: %s}" id (sP p)
  Write id expr        -> printf "%s=%s" id (sE expr)
  AwaitExt ext         -> printf "?%s" ext
  EmitExt ext Nothing  -> printf "!%s" ext
  EmitExt ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitInt int         -> printf "?%s" int
  EmitInt int          -> printf "!%s" int
  Break                -> "break"
  If expr p q          -> printf "(if %s then %s else %s)"
                            (sE expr) (sP p) (sP q)
  Seq p q              -> printf "%s; %s" (sP p) (sP q)
  Loop p               -> printf "(loop %s)" (sP p)
  Every evt p          -> printf "(every %s %s)" evt (sP p)
  And p q              -> printf "(%s && %s)" (sP p) (sP q)
  Or p q               -> printf "(%s || %s)" (sP p) (sP q)
  Pause var p          -> printf "(pause %s %s)" var (sP p)
  Fin p                -> printf "(fin %s)" (sP p)
  Nop                  -> "nop"
  Error _              -> "err"
  where
    sE = showExp
    sP = showProg

-- Checks if program is valid.
checkProg :: Stmt -> Bool
checkProg stmt = case stmt of
  Var _ p      -> checkProg p
  Int _ p      -> checkProg p
  If _ p q     -> checkProg p && checkProg q
  Seq p q      -> checkProg p && checkProg q
  Loop p       -> checkLoop (Loop p) && checkProg p
  Every e p    -> checkEvery (Every e p) && checkProg p
  And p q      -> checkProg p && checkProg q
  Or p q       -> checkProg p && checkProg q
  Pause _ p    -> checkProg p
  Fin p        -> checkFin (Fin p) && checkProg p
  _            -> True

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Break/AwaitExt/Every.
checkLoop :: Stmt -> Bool
checkLoop loop = case loop of
  Loop body    -> cL False body
  _            -> error "checkLoop: expected Loop"
  where
    cL ignBrk stmt = case stmt of
      AwaitExt _   -> True
      Break        -> not ignBrk
      Every _ _    -> True
      Var _ p      -> cL ignBrk p
      Int _ p      -> cL ignBrk p
      If _ p q     -> cL ignBrk p && cL ignBrk q
      Seq p q      -> cL ignBrk p || cL ignBrk q
      Loop p       -> cL True p
      And p q      -> cL ignBrk p && cL ignBrk q
      Or p q       -> cL ignBrk p && cL ignBrk q
      Pause _ p    -> cL ignBrk p
      Fin p        -> False       -- runs in zero time
      _            -> False

-- Receives a Fin or Every statement and checks whether it does not contain
-- any occurrences of Loop/Break/Await*/Every/Fin.
checkFin :: Stmt -> Bool
checkFin finOrEvery = case finOrEvery of
  Fin body     -> cF body
  Every _ body -> cF body
  _            -> error "checkFin: expected Fin or Every"
  where
    cF stmt = case stmt of
      Break        -> False
      AwaitInt _   -> False
      AwaitExt _   -> False
      Every _ _    -> False
      Fin _        -> False
      Loop _       -> False
      Var _ p      -> cF p
      Int _ p      -> cF p
      If _ p q     -> cF p && cF q
      Seq p q      -> cF p && cF q
      And p q      -> cF p && cF q
      Or p q       -> cF p && cF q
      Pause _ p    -> cF p
      _            -> True

-- Alias for checkFin.
checkEvery :: Stmt -> Bool
checkEvery = checkFin

simplify :: Stmt -> Stmt

simplify (Var id p) =
  case p' of
    Nop   -> Nop
    Break -> Break
    otherwise -> Var id p'
  where p' = simplify p

simplify (Int id p) =
  case p' of
    Nop   -> Nop
    Break -> Break
    otherwise -> Int id p'
  where p' = simplify p

simplify (If exp p q) =
  if p' == q' then p' else (If exp p' q')
  where p' = simplify p
        q' = simplify q

simplify (Seq p q) =
  case (p',q') of
    (Nop,   q')  -> q'
    (p',    Nop) -> p'
    (Break, q')  -> Break
    otherwise    -> Seq p' q'
  where p' = simplify p
        q' = simplify q

simplify (Loop p) =
  case p' of
    Break     -> Nop
    otherwise -> Loop p'
  where p' = simplify p

simplify (Every evt p) = (Every evt (simplify p))

simplify (And p q) =
  case (p',q') of
    (Nop,   q')  -> q'
    (p',    Nop) -> p'
    (Break, q')  -> Break
    otherwise    -> And p' q'
  where p' = simplify p
        q' = simplify q

simplify (Or p q) =
  case (p',q') of
    (AwaitExt "FOREVER", q') -> q'
    (p', AwaitExt "FOREVER") -> p'
    (Nop,   q') -> Nop
    (Break, q') -> Break
    otherwise   -> Or p' q'
  where p'  = simplify p
        q'  = simplify q

simplify (Pause id p) =
  case p' of
    Nop   -> Nop
    Break -> Break
    otherwise -> Pause id p'
  where p' = simplify p

simplify (Fin p) =
  case p' of
    Nop       -> Nop
    otherwise -> Fin p'
  where p' = simplify p

simplify p = p
