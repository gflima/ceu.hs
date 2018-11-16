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
  | If Exp Stmt Stmt            -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every ID_Evt Stmt           -- event iteration
  | Par Stmt Stmt               -- par statement
  | Pause ID_Var Stmt           -- pause/suspend statement
  | Fin Stmt                    -- finalization statement
  | Trap Stmt                   -- enclose escape
  | Escape Int                  -- escape N traps
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Par`                  -- `Par` associates to the right

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
  If expr p q          -> printf "(if %s then %s else %s)"
                            (sE expr) (sP p) (sP q)
  Seq p q              -> printf "%s; %s" (sP p) (sP q)
  Loop p               -> printf "(loop %s)" (sP p)
  Every evt p          -> printf "(every %s %s)" evt (sP p)
  Par p q              -> printf "(%s || %s)" (sP p) (sP q)
  Pause var p          -> printf "(pause %s %s)" var (sP p)
  Fin p                -> printf "(fin %s)" (sP p)
  Trap p               -> printf "(trap %s)" (sP p)
  Escape n             -> printf "(escape %d)" n
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
  Par p q      -> checkProg p && checkProg q
  Pause _ p    -> checkProg p
  Fin p        -> checkFin (Fin p) && checkProg p
  Trap p       -> checkProg p
  _            -> True

-- Receives a Loop statement and checks whether all execution paths
-- in its body lead to an occurrence of a matching-Escape/AwaitExt/Every.
checkLoop :: Stmt -> Bool
checkLoop loop = case loop of
  Loop body    -> cL 0 body
  _            -> error "checkLoop: expected Loop"
  where
    cL n stmt = case stmt of
      AwaitExt _       -> True
      Every _ _        -> True
      Var _ p          -> cL n p
      Int _ p          -> cL n p
      If _ p q         -> cL n p && cL n q
      Seq (Escape k) q -> cL n (Escape k)   -- q never executes
      Seq p q          -> cL n p || cL n q
      Loop p           -> cL n p
      Par p q          -> cL n p && cL n q
      Pause _ p        -> cL n p
      Trap p           -> cL (n+1) p
      Escape k        -> (k >= n)
      _                -> False

-- Receives a Fin or Every statement and checks whether it does not contain
-- any occurrences of Loop/Break/Await*/Every/Fin.
checkFin :: Stmt -> Bool
checkFin finOrEvery = case finOrEvery of
  Fin body     -> cF body
  Every _ body -> cF body
  _            -> error "checkFin: expected Fin or Every"
  where
    cF stmt = case stmt of
      AwaitInt _   -> False
      AwaitExt _   -> False
      Every _ _    -> False
      Fin _        -> False
      Loop _       -> False
      Var _ p      -> cF p
      Int _ p      -> cF p
      If _ p q     -> cF p && cF q
      Seq p q      -> cF p && cF q
      Par p q      -> cF p && cF q
      Pause _ p    -> cF p
      Trap p       -> cF p
      Escape _     -> False
      _            -> True

-- Alias for checkFin.
checkEvery :: Stmt -> Bool
checkEvery = checkFin

-- checkEscape

checkEscape :: Stmt -> Bool
checkEscape p = cE (-1) p where
  cE :: Int -> Stmt -> Bool
  cE n (Var _ p)     = (cE n p)
  cE n (Int _ p)     = (cE n p)
  cE n (If _ p1 p2)  = (cE n p1) && (cE n p2)
  cE n (Seq p1 p2)   = (cE n p1) && (cE n p2)
  cE n (Loop p)      = (cE (n+1) p)
  cE n (Every _ p)   = (cE n p)
  cE n (Par p1 p2)   = (cE n p1) && (cE n p2)
  cE n (Pause _ p)   = (cE n p)
  cE n (Fin p)       = (cE n p)
  cE n (Trap p)      = (cE (n+1) p)
  cE n (Escape k)
    | (n >= k)       = True
    | otherwise      = False --error "checkEscape: `escape` without `trap`"
  cE n p             = True
