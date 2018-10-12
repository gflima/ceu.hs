module Ceu.FullGrammar where

import qualified Ceu.Grammar as G

-- Program (pg 5).
data Stmt
  = Block Stmt                  -- declaration block
  | Var G.ID                    -- variable declaration
  | Write G.ID G.Expr           -- assignment statement
  | AwaitExt G.Evt              -- await external event
  | AwaitInt G.Evt              -- await internal event
  | EmitInt G.Evt               -- emit internal event
  | Break                       -- loop escape
  | If G.Expr Stmt Stmt         -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every G.Evt Stmt            -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Spawn Stmt                  -- spawn statement
  | Finalize Stmt               -- finalize statement
  | Async Stmt                  -- async statement
  | Block' [G.ID] Stmt
  | Nop
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remVars: Removes (Var id) stmts and maps (Block p) -> (Block' [ids] p)

remVar :: Stmt -> ([G.ID], Stmt)
remVar (Block p)      = ([], Block' ids' p') where (ids', p') = remVar p
remVar (Var id')      = ([id'], Nop)
remVar (If exp p1 p2) = remVar2 p1 p2 (\p1' p2' -> If exp p1' p2')
remVar (Seq p1 p2)    = remVar2 p1 p2 (\p1' p2' -> Seq p1' p2')
remVar (Loop p)       = remVar1 p (\p' -> Loop p')
remVar (Every e p)    = remVar1 p (\p' -> Every e p')
remVar (And p1 p2)    = remVar2 p1 p2 (\p1' p2' -> And p1' p2')
remVar (Or p1 p2)     = remVar2 p1 p2 (\p1' p2' -> Or  p1' p2')
remVar (Finalize p)   = remVar1 p (\p' -> Finalize p')
remVar (Async p)      = remVar1 p (\p' -> Async p')
remVar q              = ([], q)

remVar1 :: Stmt -> (Stmt->Stmt) -> ([G.ID], Stmt)
remVar1 p f = (ids', f p') where (ids',p') = remVar p

remVar2 :: Stmt -> Stmt -> (Stmt->Stmt->Stmt) -> ([G.ID], Stmt)
remVar2 p1 p2 f = (ids1'++ids2', f p1' p2') where
                  (ids1',p1') = remVar p1
                  (ids2',p2') = remVar p2

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG p' where
  (_, p') = remVar (Block (Seq (Var "ret") p))

  toG :: Stmt -> G.Stmt
  toG (Write id exp) = G.Write id exp
  toG (AwaitExt e)   = G.AwaitExt e
  toG (AwaitInt e)   = G.AwaitInt e
  toG Break          = G.Break
  toG (If e p1 p2)   = G.If e (toG p1) (toG p2)
  toG (Seq p1 p2)    = G.Seq (toG p1) (toG p2)
  toG (Loop p)       = G.Loop (toG p)
  toG (Every e p)    = G.Every e (toG p)
  toG (And p1 p2)    = G.And (toG p1) (toG p2)
  toG (Or p1 p2)     = G.Or (toG p1) (toG p2)
  --toG (Finalize p)   = ...
  --toG (Async Stmt)   = ...
  toG (Block' ids p) = G.Block ids (toG p)
  toG Nop            = G.Nop
