module Ceu.Full.Grammar where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval as E
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
  | Error String                        -- generate runtime error (for testing purposes)
  | Par' Stmt Stmt                      -- par as in basic Grammar
  | Pause' ID_Var Stmt                  -- pause as in basic Grammar
  | Fin' Stmt                           -- fin as in basic Grammar
  | Trap' Stmt                          -- trap as in basic Grammar
  | Escape' Int                         -- escape as in basic Grammar
  | Nop                                 -- nop as in basic Grammar
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right
