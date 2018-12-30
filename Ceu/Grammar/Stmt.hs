module Ceu.Grammar.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, annz)
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

getAnnS :: Stmt -> Ann
getAnnS (Var      z _ _ _)   = z
getAnnS (Inp      z _ _)     = z
getAnnS (Out      z _ _)     = z
getAnnS (Evt      z _ _)     = z
getAnnS (Func     z _ _ _)   = z
getAnnS (FuncI    z _ _ _ _) = z
getAnnS (Write    z _ _)     = z
getAnnS (AwaitInp z _)       = z
getAnnS (EmitExt  z _ _)     = z
getAnnS (AwaitEvt z _)       = z
getAnnS (EmitEvt  z _)       = z
getAnnS (If       z _ _ _)   = z
getAnnS (Seq      z _ _)     = z
getAnnS (Loop     z _)       = z
getAnnS (Every    z _ _)     = z
getAnnS (Par      z _ _)     = z
getAnnS (Pause    z _ _)     = z
getAnnS (Fin      z _)       = z
getAnnS (Trap     z _)       = z
getAnnS (Escape   z _)       = z
getAnnS (Nop      z)         = z
getAnnS (Halt     z)         = z
getAnnS (RawS     z _)       = z
getAnnS (Error    z _)       = z

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
