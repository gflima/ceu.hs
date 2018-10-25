module Ceu.Grammar where

import Ceu.Globals
import Text.Printf

-- Program (pg 5).
data Stmt
  = Var ID_Var Stmt             -- variable declaration
  | Evt ID_Var Stmt             -- event declaration
  | Write ID_Var Expr           -- assignment statement
  | AwaitExt ID_Evt             -- await external event
  | AwaitInt ID_Evt             -- await internal event
  | EmitInt ID_Evt              -- emit internal event
  | Break                       -- loop escape
  | If Expr Stmt Stmt           -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every ID_Evt Stmt           -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
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
  Var id p          -> printf "{%s: %s}" id (sP p)
  Evt id p          -> printf "{%s: %s}" id (sP p)
  Write id expr     -> printf "%s=%s" id (sE expr)
  AwaitExt e        -> printf "?E%s" e
  AwaitInt e        -> printf "?%s" e
  EmitInt e         -> printf "!%s" e
  Break             -> "break"
  If expr p q       -> printf "(if %s then %s else %s)"
                       (sE expr) (sP p) (sP q)
  Seq p q           -> printf "%s; %s" (sP p) (sP q)
  Loop p            -> printf "(loop %s)" (sP p)
  Every e p         -> printf "(every %s %s)" e (sP p)
  And p q           -> printf "(%s && %s)" (sP p) (sP q)
  Or p q            -> printf "(%s || %s)" (sP p) (sP q)
  Fin p             -> printf "(fin %s)" (sP p)
  Nop               -> "nop"
  Error _           -> "err"
  where
    sE = showExpr
    sP = showProg

-- Checks if program is valid.
checkProg :: Stmt -> Bool
checkProg stmt = case stmt of
  Var _ p      -> checkProg p
  Evt _ p      -> checkProg p
  If _ p q     -> checkProg p && checkProg q
  Seq p q      -> checkProg p && checkProg q
  Loop p       -> checkLoop (Loop p) && checkProg p
  Every e p    -> checkEvery (Every e p) && checkProg p
  And p q      -> checkProg p && checkProg q
  Or p q       -> checkProg p && checkProg q
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
      Evt _ p      -> cL ignBrk p
      If _ p q     -> cL ignBrk p && cL ignBrk q
      Seq p q      -> cL ignBrk p || cL ignBrk q
      Loop p       -> cL True p
      And p q      -> cL ignBrk p && cL ignBrk q
      Or p q       -> cL ignBrk p && cL ignBrk q
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
      Evt _ p      -> cF p
      If _ p q     -> cF p && cF q
      Seq p q      -> cF p && cF q
      And p q      -> cF p && cF q
      Or p q       -> cF p && cF q
      _            -> True

-- Alias for checkFin.
checkEvery :: Stmt -> Bool
checkEvery = checkFin
