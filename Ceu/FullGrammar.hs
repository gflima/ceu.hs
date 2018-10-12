module Ceu.FullGrammar where

import qualified Ceu.Grammar as G

-- Program (pg 5).
data Stmt
  = Block Stmt                  -- declaration block
  | Var G.ID                    -- variable declaration
  | Write G.ID G.Expr           -- assignment statement
  | AwaitExt G.Evt              -- await external event
  | AwaitFor                    -- await forever
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
  | Block' [G.ID] Stmt          -- block as in basic Grammar
  | Fin' Stmt                   -- fin as in basic Grammar
  | Nop'                        -- nop as in basic Grammar
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remVar: Removes (Var id) stmts and maps (Block p) -> (Block' [ids] p)

remVar :: Stmt -> Stmt
remVar (Block p) = p' where
    (_,p') = rV (Block p)

    rV :: Stmt -> ([G.ID], Stmt)
    rV (Block p)      = ([], Block' ids' p') where (ids', p') = rV p
    rV (Var id)       = ([id], Nop')
    rV (If exp p1 p2) = rV2 p1 p2 (\p1' p2' -> If exp p1' p2')
    rV (Seq p1 p2)    = rV2 p1 p2 (\p1' p2' -> Seq p1' p2')
    rV (Loop p)       = rV1 p (\p' -> Loop p')
    rV (Every e p)    = rV1 p (\p' -> Every e p')
    rV (And p1 p2)    = rV2 p1 p2 (\p1' p2' -> And p1' p2')
    rV (Or p1 p2)     = rV2 p1 p2 (\p1' p2' -> Or  p1' p2')
    rV (Spawn p)      = rV1 p (\p' -> Spawn p')
    rV (Finalize p)   = rV1 p (\p' -> Finalize p')
    rV (Async p)      = rV1 p (\p' -> Async p')
    rV (Block' _ _)   = error "remVar: unexpected statement (Block')"
    rV (Fin' p)       = rV1 p (\p' -> Fin' p')
    rV q              = ([], q)

    rV1 :: Stmt -> (Stmt->Stmt) -> ([G.ID], Stmt)
    rV1 p f = (ids', f p') where (ids',p') = rV p

    rV2 :: Stmt -> Stmt -> (Stmt->Stmt->Stmt) -> ([G.ID], Stmt)
    rV2 p1 p2 f = (ids1'++ids2', f p1' p2') where
                      (ids1',p1') = rV p1
                      (ids2',p2') = rV p2

remVar _         = error "remVar: expected enclosing top-level block"

-- remSpawn: Converts (spawn p1; p2) into (p1;AwaitFor or p2)

remSpawn :: Stmt -> Stmt
remSpawn (Block p)           = Block (remSpawn p)
remSpawn (If e p1 p2)        = If e (remSpawn p1) (remSpawn p2)
remSpawn (Seq (Spawn p1) p2) = Or (Seq (remSpawn p1) AwaitFor) (remSpawn p2)
remSpawn (Seq p1 p2)         = Seq (remSpawn p1) (remSpawn p2)
remSpawn (Loop p)            = Loop (remSpawn p)
remSpawn (Every e p)         = Every e (remSpawn p)
remSpawn (And p1 p2)         = And (remSpawn p1) (remSpawn p2)
remSpawn (Or p1 p2)          = Or (remSpawn p1) (remSpawn p2)
remSpawn (Spawn p)           = error "remSpawn: unexpected statement (Spawn)"
remSpawn (Finalize p)        = Finalize (remSpawn p)
remSpawn (Async p)           = Async (remSpawn p)
remSpawn (Block' ids p)      = Block' ids (remSpawn p)
remSpawn (Fin' p)            = Fin' (remSpawn p)
remSpawn p                   = p

-- chkSpawn: `Spawn` can only appear as first item in `Seq`

chkSpawn :: Stmt -> Stmt
chkSpawn p = case p of
  (Spawn _) -> error "chkSpawn: unexpected statement (Spawn)"
  _ | (chkS p) -> p
    | otherwise -> error "chkSpawn: unexpected statement (Spawn)"
  where

  notS (Spawn _) = False
  notS p         = True

  chkS :: Stmt -> Bool
  chkS (Block p)           = (notS p) && (chkS p)
  chkS (If e p1 p2)        = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Seq p1 p2)         = (chkS p1) && (notS p2) && (chkS p2)
  chkS (Loop p)            = (notS p) && (chkS p)
  chkS (Every e p)         = (notS p) && (chkS p)
  chkS (And p1 p2)         = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Or p1 p2)          = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Spawn p)           = (notS p) && (chkS p)
  chkS (Finalize p)        = (notS p) && (chkS p)
  chkS (Async p)           = (notS p) && (chkS p)
  chkS (Block' ids p)      = (notS p) && (chkS p)
  chkS (Fin' p)            = (notS p) && (chkS p)
  chkS _                   = True

-- remAwaitFor: Converts AwaitFor into (AwaitExt inputForever)

remAwaitFor :: Stmt -> Stmt
remAwaitFor (Block p)           = Block (remAwaitFor p)
remAwaitFor (If e p1 p2)        = If e (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Seq p1 p2)         = Seq (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Loop p)            = Loop (remAwaitFor p)
remAwaitFor (Every e p)         = Every e (remAwaitFor p)
remAwaitFor (And p1 p2)         = And (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Or p1 p2)          = Or (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Spawn p)           = Spawn (remAwaitFor p)
remAwaitFor (Finalize p)        = Finalize (remAwaitFor p)
remAwaitFor (Async p)           = Async (remAwaitFor p)
remAwaitFor (Block' ids p)      = Block' ids (remAwaitFor p)
remAwaitFor (Fin' p)            = Fin' (remAwaitFor p)
remAwaitFor AwaitFor            = AwaitExt G.inputForever
remAwaitFor p                   = p

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG $ remAwaitFor $ remSpawn $ chkSpawn $ remVar (Block (Seq (Var "ret") p)) where
  toG :: Stmt -> G.Stmt
  toG (Write id exp) = G.Write id exp
  toG (AwaitExt e)   = G.AwaitExt e
  toG (AwaitInt e)   = G.AwaitInt e
  toG (EmitInt e)    = G.EmitInt e
  toG Break          = G.Break
  toG (If e p1 p2)   = G.If e (toG p1) (toG p2)
  toG (Seq p1 p2)    = G.Seq (toG p1) (toG p2)
  toG (Loop p)       = G.Loop (toG p)
  toG (Every e p)    = G.Every e (toG p)
  toG (And p1 p2)    = G.And (toG p1) (toG p2)
  toG (Or p1 p2)     = G.Or (toG p1) (toG p2)
  toG (Block' ids p) = G.Block ids (toG p)
  toG (Fin' p)       = G.Fin (toG p)
  toG Nop'           = G.Nop
  toG _              = error "toG: unexpected statement (Block,Var,AwaitFor,Finalize,Spawn,Async)"
