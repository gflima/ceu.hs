module Ceu.Grammar where

-- Primitive types.
type Evt = Int                  -- event identifier
type ID  = String               -- variable identifier
type Val = Int                  -- value

-- Expression.
data Expr
  = Const Val                   -- constant
  | Read ID                     -- contents
  | Umn Expr                    -- unary minus
  | Add Expr Expr               -- addition
  | Sub Expr Expr               -- subtraction
  deriving (Eq, Show)

infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left

-- Program (pg 5).
data Stmt
  = Block [ID] Stmt             -- declaration block
  | Write ID Expr               -- assignment statement
  | AwaitExt Evt                -- await external event
  | AwaitInt Evt                -- await internal event
  | EmitInt Evt                 -- emit internal event
  | Break                       -- loop escape
  | If Expr Stmt Stmt           -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every Evt Stmt              -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Fin Stmt                    -- finalization statement
  | Nop                         -- dummy statement (internal)
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
  (Const n)   -> show n
  (Read v)    -> v
  (Umn e)     -> "-(" ++ showExpr e ++ ")"
  (Add e1 e2) -> "(" ++ showExpr e1 ++ "+" ++ showExpr e2 ++ ")"
  (Sub e1 e2) -> "(" ++ showExpr e1 ++ "-" ++ showExpr e2 ++ ")"

-- Shows list of variables.
showVars :: [ID] -> String
showVars vars = case vars of
  []       -> ""
  (v:[])   -> v
  (v:vars) -> v ++ "," ++ showVars vars

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case stmt of
  Block vars p   -> "{" ++ (if null vars then ""
                               else showVars vars ++ ": ")
                      ++ showProg p ++ "}"
  Write var expr -> var ++ "=" ++ showExpr expr
  AwaitExt e     -> "?E" ++ show e
  AwaitInt e     -> "?" ++ show e
  EmitInt e      -> "!" ++ show e
  Break          -> "break"
  If expr p q    -> "(if " ++ showExpr expr ++ " then "
                      ++ showProg p ++ " else " ++ showProg q ++ ")"
  Seq p q        -> showProg p ++ "; " ++ showProg q
  Loop p         -> "(loop " ++ showProg p ++ ")"
  Every e p      -> "(every " ++ show e ++ " " ++ showProg p ++ ")"
  And p q        -> "(" ++ showProg p ++ " && " ++ showProg q ++ ")"
  Or p q         -> "(" ++ showProg p ++ " || " ++ showProg q ++ ")"
  Fin p          -> "(fin " ++ showProg p ++ ")"
  Nop            -> "nop"
  CanRun n       -> "@canrun(" ++ show n ++ ")"
  Restore n      -> "@restore(" ++ show n ++ ")"
  Loop' p q      -> "(" ++ showProg p ++ " @loop " ++ showProg q ++ ")"
  And' p q       -> "(" ++ showProg p ++ " @&& " ++ showProg q ++ ")"
  Or' p q        -> "(" ++ showProg p ++ " @|| " ++ showProg q ++ ")"

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
  Loop body    -> checkLoop' False body
  Loop' _ body -> checkLoop' False body
  _            -> error "checkLoop: expected Loop or Loop'"
  where
    checkLoop' :: Bool -> Stmt -> Bool
    checkLoop' ignBrk stmt = case stmt of
      AwaitExt _ -> True
      Break      -> not ignBrk
      Every _ _  -> True
      Block _ p  -> checkLoop' ignBrk p
      If _ p q   -> checkLoop' ignBrk p && checkLoop' ignBrk q
      Seq p q    -> checkLoop' ignBrk p || checkLoop' ignBrk q
      Loop p     -> checkLoop' True p
      And p q    -> checkLoop' ignBrk p && checkLoop' ignBrk q
      Or p q     -> checkLoop' ignBrk p && checkLoop' ignBrk q
      Fin p      -> False       -- always run in zero time
      Loop' p q  -> checkLoop' True p && checkLoop' True q
      And' p q   -> checkLoop' ignBrk p && checkLoop' ignBrk q
      Or' p q    -> checkLoop' ignBrk p && checkLoop' ignBrk q
      _          -> False

-- Receives a Fin or Every statement and checks whether it does not contain
-- any occurrences of Loop/Break/Await*/Every/Fin.
checkFin :: Stmt -> Bool
checkFin finOrEvery = case finOrEvery of
  Fin body     -> checkFin' body
  Every _ body -> checkFin' body
  _            -> error "checkFin: expected Fin or Every"
  where
    checkFin' :: Stmt -> Bool
    checkFin' stmt = case stmt of
      Break      -> False
      AwaitInt _ -> False
      AwaitExt _ -> False
      Every _ _  -> False
      Fin _      -> False
      Loop _     -> False
      Loop' _ _  -> False
      Block _ p  -> checkFin' p
      If _ p q   -> checkFin' p && checkFin' q
      Seq p q    -> checkFin' p && checkFin' q
      And p q    -> checkFin' p && checkFin' q
      Or p q     -> checkFin' p && checkFin' q
      And' p q   -> checkFin' p && checkFin' q
      Or' p q    -> checkFin' p && checkFin' q
      _          -> True

-- Alias for checkFin.
checkEvery :: Stmt -> Bool
checkEvery = checkFin
