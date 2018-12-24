module Ceu.Grammar.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp (Exp(..), showExp)
import Text.Printf

-- Program (pg 5).
data Stmt ann
  = Var      ann ID_Var (Stmt ann)                  -- variable declaration
  | Inp      ann ID_Inp (Stmt ann)                  -- input declaration
  | Out      ann ID_Out (Stmt ann)                  -- output declaration
  | Evt      ann ID_Evt (Stmt ann)                  -- event declaration
  | Write    ann ID_Var (Exp ann)                   -- assignment statement
  | AwaitInp ann ID_Inp                             -- await external event
  | EmitExt  ann ID_Ext (Maybe (Exp ann))           -- emit external event
  | AwaitEvt ann ID_Evt                             -- await internal event
  | EmitEvt  ann ID_Evt                             -- emit internal event
  | If       ann (Exp ann) (Stmt ann) (Stmt ann)    -- conditional
  | Seq      ann (Stmt ann) (Stmt ann)              -- sequence
  | Loop     ann (Stmt ann)                         -- infinite loop
  | Every    ann ID (Stmt ann)                      -- event iteration
  | Par      ann (Stmt ann) (Stmt ann)              -- par statement
  | Pause    ann ID_Var (Stmt ann)                  -- pause/suspend statement
  | Fin      ann (Stmt ann)                         -- finalization statement
  | Trap     ann (Stmt ann)                         -- enclose escape
  | Escape   ann Int                                -- escape N traps
  | Nop      ann                                    -- dummy statement (internal)
  | Halt     ann                                    -- halt (await FOREVER)
  | Error    ann String                             -- generate runtime error (for testing)
  deriving (Eq, Show)

sSeq a b = Seq () a b
sPar a b = Par () a b

infixr 1 `sSeq` -- `Seq` associates to the right
infixr 0 `sPar` -- `Par` associates to the right

getAnn :: Stmt ann -> ann
getAnn (Var      z _ _)   = z
getAnn (Inp      z _ _)   = z
getAnn (Out      z _ _)   = z
getAnn (Evt      z _ _)   = z
getAnn (Write    z _ _)   = z
getAnn (AwaitInp z _)     = z
getAnn (EmitExt  z _ _)   = z
getAnn (AwaitEvt z _)     = z
getAnn (EmitEvt  z _)     = z
getAnn (If       z _ _ _) = z
getAnn (Seq      z _ _)   = z
getAnn (Loop     z _)     = z
getAnn (Every    z _ _)   = z
getAnn (Par      z _ _)   = z
getAnn (Pause    z _ _)   = z
getAnn (Fin      z _)     = z
getAnn (Trap     z _)     = z
getAnn (Escape   z _)     = z
getAnn (Nop      z)       = z
getAnn (Halt     z)       = z
getAnn (Error    z _)     = z

-- Shows program.
showProg :: (Stmt ann) -> String
showProg stmt = case stmt of
  Var      _ id p         -> printf "{%s: %s}" id (sP p)
  Inp      _ id p         -> printf "{%s: %s}" id (sP p)
  Out      _ id p         -> printf "{%s: %s}" id (sP p)
  Evt      _ id p         -> printf "{%s: %s}" id (sP p)
  Write    _ id expr      -> printf "%s=%s" id (sE expr)
  AwaitInp _ ext          -> printf "?%s" ext
  EmitExt  _ ext Nothing  -> printf "!%s" ext
  EmitExt  _ ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitEvt _ int          -> printf "?%s" int
  EmitEvt  _ int          -> printf "!%s" int
  If       _ expr p q     -> printf "(if %s then %s else %s)"
                               (sE expr) (sP p) (sP q)
  Seq      _ p q          -> printf "%s; %s" (sP p) (sP q)
  Loop     _ p            -> printf "(loop %s)" (sP p)
  Every    _ evt p        -> printf "(every %s %s)" evt (sP p)
  Par      _ p q          -> printf "(%s || %s)" (sP p) (sP q)
  Pause    _ var p        -> printf "(pause %s %s)" var (sP p)
  Fin      _ p            -> printf "(fin %s)" (sP p)
  Trap     _ p            -> printf "(trap %s)" (sP p)
  Escape   _ n            -> printf "(escape %d)" n
  Nop      _              -> "nop"
  Halt     _              -> "halt"
  Error    _ _            -> "err"
  where
    sE = showExp
    sP = showProg

stmt2word :: (Stmt ann) -> String
stmt2word stmt = case stmt of
  Var _ _ _     -> "declaration"
  Inp _ _ _     -> "declaration"
  Out _ _ _     -> "declaration"
  Evt _ _ _     -> "declaration"
  Write _ _ _   -> "assignment"
  AwaitInp _ _  -> "await"
  EmitExt _ _ _ -> "emit"
  AwaitEvt _ _  -> "await"
  EmitEvt _ _   -> "emit"
  If _ _ _ _    -> "if"
  Seq _ _ _     -> "sequence"
  Loop _ _      -> "loop"
  Every _ _ _   -> "every"
  Par _ _ _     -> "parallel"
  Pause _ _ _   -> "pause/if"
  Fin _ _       -> "finalize"
  Trap _ _      -> "trap"
  Escape _ _    -> "escape"
  Nop _         -> "nop"
  Halt _        -> "halt"
  Error _ _     -> "error"

instance (Ann ann) => INode (Stmt ann) where
  toWord   = stmt2word
  toSource = getSource . getAnn
  toN      = getN . getAnn
  toTrails = getTrails . getAnn
