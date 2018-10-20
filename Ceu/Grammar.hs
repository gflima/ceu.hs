module Ceu.Grammar where

import Text.Printf

-- Primitive types.
type Evt = String               -- event identifier
type ID  = String               -- variable identifier
type Val = Int                  -- value

-- Special events:
-- "BOOT"
-- "FOREVER"

-- Expression.
data Expr
  = Const Val                   -- constant
  | Read ID                     -- variable read
  | Umn Expr                    -- unary minus
  | Add Expr Expr               -- addition
  | Sub Expr Expr               -- subtraction
  | Mul Expr Expr               -- multiplication
  | Div Expr Expr               -- division
  deriving (Eq, Show)

infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left
infixl 7 `Mul`                  -- `Mul` associates to the left
infixl 7 `Div`                  -- `Div` associates to the left

-- Program (pg 5).
data Stmt
  = Block ([ID],[ID]) Stmt      -- declaration block
  | Write ID Expr               -- assignment statement
  | AwaitExt Evt                -- await external event
  | AwaitInt ID                 -- await internal event
  | EmitInt ID                  -- emit internal event
  | Break                       -- loop escape
  | If Expr Stmt Stmt           -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every Evt Stmt              -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Fin Stmt                    -- finalization statement
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing purposes)
  | CanRun Int                  -- wait for stack level (internal)
  | Restore Int                 -- restore environment (internal)
  | Loop' Stmt Stmt             -- unrolled Loop (internal)
  | And' Stmt Stmt              -- unrolled And (internal)
  | Or' Stmt Stmt               -- unrolled Or (internal)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- Shows expression.
showExpr :: Expr -> String
showExpr expr = case expr of
  Const n   -> show n
  Read v    -> v
  Umn e     -> printf "(-%s)" (showExpr e)
  Add e1 e2 -> printf "(%s+%s)" (showExpr e1) (showExpr e2)
  Sub e1 e2 -> printf "(%s-%s)" (showExpr e1) (showExpr e2)
  Mul e1 e2 -> printf "(%s*%s)" (showExpr e1) (showExpr e2)
  Div e1 e2 -> printf "(%s*%s)" (showExpr e1) (showExpr e2)

-- Shows list of declarations (variables or events).
showDcls :: [ID] -> String
showDcls dcls = case dcls of
  []     -> ""
  v:[]   -> v
  v:dcls -> v ++ "," ++ showDcls dcls

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Block (vs,es) p | null (vs,es) -> printf "{%s}" (sP p)
                  | otherwise    -> printf "{%s/%s: %s}" (sV vs) (sV es) (sP p)
  Write var expr -> printf "%s=%s" var (sE expr)
  AwaitExt e     -> printf "?E%s" e
  AwaitInt e     -> printf "?%s" e
  EmitInt e      -> printf "!%s" e
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
  Restore n      -> printf "@restore(%d)" n
  Loop' p q      -> printf "(%s @loop %s)" (sP p) (sP q)
  And' p q       -> printf "(%s @&& %s)" (sP p) (sP q)
  Or' p q        -> printf "(%s @|| %s)" (sP p) (sP q)
  where
    sE = showExpr
    sP = showProg
    sV = showDcls

-- Checks if program is valid.
checkProg :: Stmt -> Bool
checkProg stmt = case stmt of
  Block _ p -> checkProg p
  If _ p q  -> checkProg p && checkProg q
  Seq p q   -> checkProg p && checkProg q
  Loop p    -> checkLoop (Loop p) && checkProg p
  Every e p -> checkEvery (Every e p) && checkProg p
  And p q   -> checkProg p && checkProg q
  Or p q    -> checkProg p && checkProg q
  Fin p     -> checkFin (Fin p) && checkProg p
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
      Block _ p  -> cL ignBrk p
      If _ p q   -> cL ignBrk p && cL ignBrk q
      Seq p q    -> cL ignBrk p || cL ignBrk q
      Loop p     -> cL True p
      And p q    -> cL ignBrk p && cL ignBrk q
      Or p q     -> cL ignBrk p && cL ignBrk q
      Fin p      -> False       -- runs in zero time
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
      Block _ p  -> cF p
      If _ p q   -> cF p && cF q
      Seq p q    -> cF p && cF q
      And p q    -> cF p && cF q
      Or p q     -> cF p && cF q
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
  Loop' p q | checkLoop (Loop p) -> cME p         -- q is unreachable
            | otherwise          -> cME p + cME q
  And' p q                       -> cME p + cME q -- CHECK THIS! --
  Or' p q                        -> cME p + cME q -- CHECK THIS! --
  _                              -> 0
  where
    cME = countMaxEmits
