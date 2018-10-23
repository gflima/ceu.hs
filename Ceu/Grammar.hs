module Ceu.Grammar where

import Ceu.Globals
import Text.Printf

-- Program (pg 5).
data Stmt
  = Local [ID_Var] Stmt         -- declaration block
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
  | Error String                -- generate runtime error (for testing purposes)
  | CanRun Int                  -- wait for stack level (internal)
  | Local' Env Stmt             -- block with environment store
  | Loop' Stmt Stmt             -- unrolled Loop (internal)
  | And' Stmt Stmt              -- unrolled And (internal)
  | Or' Stmt Stmt               -- unrolled Or (internal)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- Shows list of variables.
showVars :: [ID_Var] -> String
showVars vars = case vars of
  []     -> ""
  v:[]   -> v
  v:vars -> v ++ "," ++ showVars vars

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Local vars p | null vars -> printf "{%s}" (sP p)
               | otherwise -> printf "{%s: %s}" (sV vars) (sP p)
  Write var expr -> printf "%s=%s" var (sE expr)
  AwaitExt e     -> printf "?E%d" e
  AwaitInt e     -> printf "?%d" e
  EmitInt e      -> printf "!%d" e
  Break          -> "break"
  If expr p q    -> printf "(if %s then %s else %s)" (sE expr) (sP p) (sP q)
  Seq p q        -> printf "%s; %s" (sP p) (sP q)
  Loop p         -> printf "(loop %s)" (sP p)
  Every e p      -> printf "(every %d %s)" e (sP p)
  And p q        -> printf "(%s && %s)" (sP p) (sP q)
  Or p q         -> printf "(%s || %s)" (sP p) (sP q)
  Fin p          -> printf "(fin %s)" (sP p)
  Nop            -> "nop"
  Error _        -> "err"
  CanRun n       -> printf "@canrun(%d)" n
  Local' env p   -> printf "(TODO)"
  Loop' p q      -> printf "(%s @loop %s)" (sP p) (sP q)
  And' p q       -> printf "(%s @&& %s)" (sP p) (sP q)
  Or' p q        -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExpr
    sP = showProg
    sV = showVars

-- Checks if program is valid.
checkProg :: Stmt -> Bool
checkProg stmt = case stmt of
  Local _ p -> checkProg p
  If _ p q  -> checkProg p && checkProg q
  Seq p q   -> checkProg p && checkProg q
  Loop p    -> checkLoop (Loop p) && checkProg p
  Every e p -> checkEvery (Every e p) && checkProg p
  And p q   -> checkProg p && checkProg q
  Or p q    -> checkProg p && checkProg q
  Fin p     -> checkFin (Fin p) && checkProg p
  Local' _ p -> checkProg p
  Loop' p q -> checkLoop (Loop' p q) && checkProg q
  And' p q  -> checkProg p && checkProg q
  Or' p q   -> checkProg p && checkProg q
  _         -> True

-- Receives a Loop or Loop' statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Break/AwaitExt/Every.
checkLoop :: Stmt -> Bool
checkLoop loop = case loop of
  Loop body    -> cL False body
  Loop' _ body -> cL False body
  _            -> error "checkLoop: expected Loop or Loop'"
  where
    cL ignBrk stmt = case stmt of
      AwaitExt _ -> True
      Break      -> not ignBrk
      Every _ _  -> True
      Local _ p  -> cL ignBrk p
      If _ p q   -> cL ignBrk p && cL ignBrk q
      Seq p q    -> cL ignBrk p || cL ignBrk q
      Loop p     -> cL True p
      And p q    -> cL ignBrk p && cL ignBrk q
      Or p q     -> cL ignBrk p && cL ignBrk q
      Fin p      -> False       -- runs in zero time
      Local' _ p -> cL ignBrk p
      Loop' p q  -> cL True p && cL True q
      And' p q   -> cL ignBrk p && cL ignBrk q
      Or' p q    -> cL ignBrk p && cL ignBrk q
      _          -> False

-- Receives a Fin or Every statement and checks whether it does not contain
-- any occurrences of Loop/Break/Await*/Every/Fin.
checkFin :: Stmt -> Bool
checkFin finOrEvery = case finOrEvery of
  Fin body     -> cF body
  Every _ body -> cF body
  _            -> error "checkFin: expected Fin or Every"
  where
    cF stmt = case stmt of
      Break      -> False
      AwaitInt _ -> False
      AwaitExt _ -> False
      Every _ _  -> False
      Fin _      -> False
      Loop _     -> False
      Loop' _ _  -> False
      Local _ p  -> cF p
      If _ p q   -> cF p && cF q
      Seq p q    -> cF p && cF q
      And p q    -> cF p && cF q
      Or p q     -> cF p && cF q
      Local' _ p -> cF p
      And' p q   -> cF p && cF q
      Or' p q    -> cF p && cF q
      _          -> True

-- Alias for checkFin.
checkEvery :: Stmt -> Bool
checkEvery = checkFin

-- Counts the maximum number of EmitInt's that can be executed in program.
-- (pot', pg 9)
countMaxEmits :: Stmt -> Int
countMaxEmits stmt = case stmt of
  EmitInt e                      -> 1
  If expr p q                    -> max (cME p) (cME q)
  Loop p                         -> cME p
  And p q                        -> cME p + cME q
  Or p q                         -> cME p + cME q
  Seq Break q                    -> 0
  Seq (AwaitExt e) q             -> 0
  Seq p q                        -> cME p + cME q
  Local' _ p                     -> cME p
  Loop' p q | checkLoop (Loop p) -> cME p         -- q is unreachable
            | otherwise          -> cME p + cME q
  And' p q                       -> cME p + cME q -- CHECK THIS! --
  Or' p q                        -> cME p + cME q -- CHECK THIS! --
  _                              -> 0
  where
    cME = countMaxEmits
