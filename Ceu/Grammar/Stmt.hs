module Ceu.Grammar.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..), RawAt)
import Text.Printf

-- Program (pg 5).
data Stmt
  = Var      Ann ID_Var Type Stmt           -- variable declaration
  | Inp      Ann ID_Inp Stmt                -- input declaration
  | Out      Ann ID_Out Stmt                -- output declaration
  | Evt      Ann ID_Evt Stmt                -- event declaration
  | Func     Ann ID_Func Type Stmt          -- function declaration
  | FuncI    Ann ID_Func Type (Maybe Stmt) Stmt -- function implementation
  | Write    Ann ID_Var Exp                 -- assignment statement
  | AwaitInp Ann ID_Inp                     -- await external event
  | EmitExt  Ann ID_Ext (Maybe Exp)         -- emit external event
  | AwaitEvt Ann ID_Evt                     -- await internal event
  | EmitEvt  Ann ID_Evt                     -- emit internal event
  | If       Ann Exp Stmt Stmt              -- conditional
  | Seq      Ann Stmt Stmt                  -- sequence
  | Loop     Ann Stmt                       -- infinite loop
  | Every    Ann ID Stmt                    -- event iteration
  | Par      Ann Stmt Stmt                  -- par statement
  | Pause    Ann ID_Var Stmt                -- pause/suspend statement
  | Fin      Ann Stmt                       -- finalization statement
  | Trap     Ann Stmt                       -- enclose escape
  | Escape   Ann Int                        -- escape N traps
  | Nop      Ann                            -- dummy statement (internal)
  | Halt     Ann                            -- halt (await FOREVER)
  | RawS     Ann [RawAt]                    -- raw/native statement
  | Error    Ann String                     -- generate runtime error (for testing)
  deriving (Eq, Show)

sSeq a b = Seq annz a b
sPar a b = Par annz a b
infixr 1 `sSeq`
infixr 0 `sPar`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Var      z _ _ _)   = z
    getAnn (Inp      z _ _)     = z
    getAnn (Out      z _ _)     = z
    getAnn (Evt      z _ _)     = z
    getAnn (Func     z _ _ _)   = z
    getAnn (FuncI    z _ _ _ _) = z
    getAnn (Write    z _ _)     = z
    getAnn (AwaitInp z _)       = z
    getAnn (EmitExt  z _ _)     = z
    getAnn (AwaitEvt z _)       = z
    getAnn (EmitEvt  z _)       = z
    getAnn (If       z _ _ _)   = z
    getAnn (Seq      z _ _)     = z
    getAnn (Loop     z _)       = z
    getAnn (Every    z _ _)     = z
    getAnn (Par      z _ _)     = z
    getAnn (Pause    z _ _)     = z
    getAnn (Fin      z _)       = z
    getAnn (Trap     z _)       = z
    getAnn (Escape   z _)       = z
    getAnn (Nop      z)         = z
    getAnn (Halt     z)         = z
    getAnn (RawS     z _)       = z
    getAnn (Error    z _)       = z

{-
stmt2word :: Stmt -> String
stmt2word stmt = case stmt of
  Var _ _ _ _    -> "declaration"
  Inp _ _ _      -> "declaration"
  Out _ _ _      -> "declaration"
  Evt _ _ _      -> "declaration"
  Func _ _ _ _   -> "declaration"
  FuncI _ _ _ _ _-> "implementation"
  Write _ _ _    -> "assignment"
  AwaitInp _ _   -> "await"
  EmitExt _ _ _  -> "emit"
  AwaitEvt _ _   -> "await"
  EmitEvt _ _    -> "emit"
  If _ _ _ _     -> "if"
  Seq _ _ _      -> "sequence"
  Loop _ _       -> "loop"
  Every _ _ _    -> "every"
  Par _ _ _      -> "parallel"
  Pause _ _ _    -> "pause/if"
  Fin _ _        -> "finalize"
  Trap _ _       -> "trap"
  Escape _ _     -> "escape"
  Nop _          -> "nop"
  Halt _         -> "halt"
  RawS _ _       -> "raw"
  Error _ _      -> "error"
-}
