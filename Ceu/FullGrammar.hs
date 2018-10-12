module Ceu.FullGrammar where

import qualified Ceu.Grammar as G

-- Primitive types.
type Evt = Int                  -- event identifier
type ID  = String               -- variable identifier
type Val = Int                  -- value

-- Expression.
data Expr
  = Const Val                   -- constant
  | Read ID                     -- variable read
  | Umn Expr                    -- unary minus
  | Add Expr Expr               -- addition
  | Sub Expr Expr               -- subtraction
  deriving (Eq, Show)

infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left

-- Program (pg 5).
data Stmt
  = Block Stmt                  -- declaration block
  | Var ID
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
  | Finalize Stmt               -- finalization statement
  | Async Stmt
  | Block' [ID] Stmt
  | Nop
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- Removes (Var id) stmts and maps (Block p) -> (Block' [ids] p)

remVars :: Stmt -> ([ID], Stmt)
remVars (Block p)      = ([], Block' ids' p') where (ids', p') = remVars p
remVars (Var id')      = ([id'], Nop)
remVars (If exp p1 p2) = remVars2 p1 p2 (\p1' p2' -> If exp p1' p2')
remVars (Seq p1 p2)    = remVars2 p1 p2 (\p1' p2' -> Seq p1' p2')
remVars (Loop p)       = remVars1 p (\p' -> Loop p')
remVars (Every e p)    = remVars1 p (\p' -> Every e p')
remVars (And p1 p2)    = remVars2 p1 p2 (\p1' p2' -> And p1' p2')
remVars (Or p1 p2)     = remVars2 p1 p2 (\p1' p2' -> Or  p1' p2')
remVars (Finalize p)   = remVars1 p (\p' -> Finalize p')
remVars (Async p)      = remVars1 p (\p' -> Async p')
remVars q              = ([], q)

remVars1 :: Stmt -> (Stmt->Stmt) -> ([ID], Stmt)
remVars1 p f = (ids', f p') where (ids',p') = remVars p

remVars2 :: Stmt -> Stmt -> (Stmt->Stmt->Stmt) -> ([ID], Stmt)
remVars2 p1 p2 f = (ids1'++ids2', f p1' p2') where
                  (ids1',p1') = remVars p1
                  (ids2',p2') = remVars p2

-- create block enclosing everything
-- remove remVars
-- convert to grammar
