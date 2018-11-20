module Ceu.Full.Grammar where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval as E
import Ceu.Full.Clear
import Debug.Trace

-- Special events:
-- "BOOT"
-- "FOREVER"
-- "ASYNC"

type In = (ID_Ext, Maybe Val)

type Fin = (Stmt, Stmt, Stmt)

-- Program (pg 5).
data Stmt
  = Var ID_Var (Maybe Fin) Stmt         -- variable declaration
  | Int ID_Int Bool Stmt                -- event declaration
  | Write ID_Var Exp                    -- assignment statement
  | AwaitExt ID_Ext (Maybe ID_Var)      -- await external event
  | EmitExt ID_Ext (Maybe Exp)          -- emit external event
  | AwaitFor                            -- await forever
  | AwaitTmr Exp                        -- await timer
  | AwaitInt ID_Int (Maybe ID_Var)      -- await internal event
  | EmitInt ID_Int (Maybe Exp)          -- emit internal event
  | Break                               -- loop escape
  | If Exp Stmt Stmt                    -- conditional
  | Seq Stmt Stmt                       -- sequence
  | Loop Stmt                           -- infinite loop
  | Every ID_Evt (Maybe ID_Var) Stmt    -- event iteration
  | And Stmt Stmt                       -- par/and statement
  | Or Stmt Stmt                        -- par/or statement
  | Spawn Stmt                          -- spawn statement
  | Pause ID_Evt Stmt                   -- pause/suspend statement
  | Fin Stmt Stmt Stmt                  -- finalize/pause/resume statement
  | Async Stmt                          -- async statement
  | Trap (Maybe ID_Var) Stmt            -- trap with optional assignment
  | Escape (Maybe (ID_Var,(Maybe Exp))) -- escape enclosing trap
  | Error String                        -- generate runtime error (for testing purposes)
  | Par' Stmt Stmt                      -- par as in basic Grammar
  | Pause' ID_Var Stmt                  -- pause as in basic Grammar
  | Fin' Stmt                           -- fin as in basic Grammar
  | Trap' Stmt                          -- trap as in basic Grammar
  | Escape' Int                         -- escape as in basic Grammar
  | Clear' String Stmt                  -- temporary statement
  | Nop                                 -- nop as in basic Grammar
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

toGrammar :: Stmt -> G.Stmt
toGrammar (Var var Nothing p) = G.Var var (toGrammar p)
toGrammar (Int int b p)       = G.Int int (toGrammar p)
toGrammar (Write var exp)     = G.Write var exp
toGrammar (AwaitExt ext var)  = G.AwaitExt ext
toGrammar (EmitExt ext exp)   = G.EmitExt ext exp
toGrammar (AwaitInt int var)  = G.AwaitInt int
toGrammar (EmitInt int val)   = G.EmitInt int
toGrammar (If exp p1 p2)      = G.If exp (toGrammar p1) (toGrammar p2)
toGrammar (Seq p1 p2)         = G.Seq (toGrammar p1) (toGrammar p2)
toGrammar (Loop p)            = G.Loop (toGrammar p)
toGrammar (Every evt var p)   = G.Every evt (toGrammar p)
toGrammar (Error msg)         = G.Error msg
toGrammar (Par' p1 p2)        = G.Par (toGrammar p1) (toGrammar p2)
toGrammar (Pause' var p)      = G.Pause var (toGrammar p)
toGrammar (Fin' p)            = G.Fin (toGrammar p)
toGrammar (Trap' p)           = G.Trap (toGrammar p)
toGrammar (Escape' n)         = G.Escape n
toGrammar (Clear' id p)       = clear id (toGrammar p)
toGrammar Nop                 = G.Nop
toGrammar p                   = error $ "toGrammar: unexpected statement: "++(show p)
