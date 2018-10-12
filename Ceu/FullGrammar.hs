module Ceu.FullGrammar where

import qualified Ceu.Grammar as G

-- Program (pg 5).
data Stmt
  = Block Stmt                  -- declaration block
  | Var G.ID
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
  | Finalize Stmt               -- finalization statement
  | Async Stmt
  | Block' [G.ID] Stmt
  | Nop
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remVars: Removes (Var id) stmts and maps (Block p) -> (Block' [ids] p)

remVars :: Stmt -> ([G.ID], Stmt)
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

remVars1 :: Stmt -> (Stmt->Stmt) -> ([G.ID], Stmt)
remVars1 p f = (ids', f p') where (ids',p') = remVars p

remVars2 :: Stmt -> Stmt -> (Stmt->Stmt->Stmt) -> ([G.ID], Stmt)
remVars2 p1 p2 f = (ids1'++ids2', f p1' p2') where
                  (ids1',p1') = remVars p1
                  (ids2',p2') = remVars p2

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG p' where
  (_, p') = remVars (Block (Seq (Var "ret") p))

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
