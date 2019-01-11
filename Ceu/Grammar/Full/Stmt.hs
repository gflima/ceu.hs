module Ceu.Grammar.Full.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..), RawAt)
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval as E
import Ceu.Grammar.Full.Clean
import Debug.Trace

-- Special events:
-- "BOOT"
-- "ASYNC"

type In = (ID_Inp, Maybe Val)

type Fin = (Stmt, Stmt, Stmt)

-- Program (pg 5).
data Stmt
  = Data     Ann ID_Hier [ID_Var] [DataCons] Bool -- new type declaration
  | Var      Ann ID_Var Type (Maybe Fin)        -- variable declaration
  | Inp      Ann ID_Inp Type                    -- output declaration
  | Out      Ann ID_Out Type                    -- output declaration
  | Evt      Ann ID_Evt Type                    -- event declaration
  | Func     Ann ID_Var Type                    -- function declaration
  | FuncI    Ann ID_Var Type Stmt               -- function implementation
  | Write    Ann Loc Exp                        -- assignment statement
  | AwaitInp Ann ID_Inp (Maybe Loc)             -- await external event
  | EmitExt  Ann ID_Ext Exp                     -- emit external event
  | AwaitTmr Ann Exp                            -- await timer
  | AwaitEvt Ann ID_Evt (Maybe Loc)             -- await internal event
  | EmitEvt  Ann ID_Evt (Maybe Exp)             -- emit internal event
  | Break    Ann                                -- loop escape
  | If       Ann Exp Stmt Stmt                  -- conditional
  | Seq      Ann Stmt Stmt                      -- sequence
  | Loop     Ann Stmt                           -- infinite loop
  | Every    Ann ID (Maybe Loc) Stmt            -- event iteration
  | And      Ann Stmt Stmt                      -- par/and statement
  | Or       Ann Stmt Stmt                      -- par/or statement
  | Par      Ann Stmt Stmt                      -- par statement
  | Spawn    Ann Stmt                           -- spawn statement
  | Pause    Ann ID Stmt                        -- pause/suspend statement
  | Fin      Ann Stmt Stmt Stmt                 -- finalize/pause/resume statement
  | Async    Ann Stmt                           -- async statement
  | Trap     Ann (Maybe ID_Var) Stmt            -- trap with optional assignment
  | Escape   Ann (Maybe ID_Var) Exp             -- escape enclosing trap
  | Scope    Ann Stmt                           -- scope for local variables
  | Error    Ann String                         -- generate runtime error (for testing purposes)
  | Data'    Ann ID_Hier [ID_Var] [DataCons] Bool Stmt -- new type declaration w/ stmts in scope
  | Var'     Ann ID_Var Type (Maybe Fin) Stmt   -- variable declaration w/ stmts in scope
  | Inp'     Ann ID_Inp Type Stmt               -- output declaration w/ stmts in scope
  | Out'     Ann ID_Out Type Stmt               -- output declaration w/ stmts in scope
  | Evt'     Ann ID_Evt Type Stmt               -- event declaration w/ stmts in scope
  | Func'    Ann ID_Func Type Stmt              -- functions declaration w/ stmts in scope
  | FuncI'   Ann ID_Func Type Stmt Stmt         -- functions implementation w/ stmts in scope
  | Or'      Ann Stmt Stmt                      -- used as an Or with possibly non-terminating trails
  | Par'     Ann Stmt Stmt                      -- par as in basic Grammar
  | Pause'   Ann ID_Var Stmt                    -- pause as in basic Grammar
  | Fin'     Ann Stmt                           -- fin as in basic Grammar
  | Trap'    Ann Stmt                           -- trap as in basic Grammar
  | Escape'  Ann Int                            -- escape as in basic Grammar
  | Clean'   Ann String Stmt                    -- temporary statement
  | Nop      Ann                                -- nop as in basic Grammar
  | Halt     Ann                                -- halt as in basic Grammar
  | RawS     Ann [RawAt]                        -- raw as in basic Grammar
  deriving (Eq, Show)

sSeq a b = Seq annz a b
sPar a b = Par annz a b
sAnd a b = And annz a b
sOr  a b = Or  annz a b
infixr 1 `sSeq`
infixr 0 `sAnd`
infixr 0 `sOr`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Data     z _ _ _ _) = z
    getAnn (Var      z _ _ _) = z
    getAnn (Inp      z _ _  ) = z
    getAnn (Out      z _ _  ) = z
    getAnn (Evt      z _ _  ) = z
    getAnn (Func     z _ _  ) = z
    getAnn (FuncI    z _ _ _) = z
    getAnn (Write    z _ _  ) = z
    getAnn (AwaitInp z _ _  ) = z
    getAnn (EmitExt  z _ _  ) = z
    getAnn (AwaitTmr z _    ) = z
    getAnn (AwaitEvt z _ _  ) = z
    getAnn (EmitEvt  z _ _  ) = z
    getAnn (Break    z      ) = z
    getAnn (If       z _ _ _) = z
    getAnn (Seq      z _ _  ) = z
    getAnn (Loop     z _    ) = z
    getAnn (Every    z _ _ _) = z
    getAnn (And      z _ _  ) = z
    getAnn (Or       z _ _  ) = z
    getAnn (Par      z _ _  ) = z
    getAnn (Spawn    z _    ) = z
    getAnn (Pause    z _ _  ) = z
    getAnn (Fin      z _ _ _) = z
    getAnn (Async    z _    ) = z
    getAnn (Trap     z _ _  ) = z
    getAnn (Escape   z _ _  ) = z
    getAnn (Scope    z _    ) = z
    getAnn (Error    z _    ) = z
    getAnn (Data'    z _ _ _ _ _) = z
    getAnn (Var'     z _ _ _ _) = z
    getAnn (Inp'     z _ _ _) = z
    getAnn (Out'     z _ _ _) = z
    getAnn (Evt'     z _ _ _) = z
    getAnn (Func'    z _ _ _) = z
    getAnn (FuncI'   z _ _ _ _) = z
    getAnn (Or'      z _ _  ) = z
    getAnn (Par'     z _ _  ) = z
    getAnn (Pause'   z _ _  ) = z
    getAnn (Fin'     z _    ) = z
    getAnn (Trap'    z _    ) = z
    getAnn (Escape'  z _    ) = z
    getAnn (Clean'   z _ _  ) = z
    getAnn (Nop      z      ) = z
    getAnn (Halt     z      ) = z
    getAnn (RawS     z _    ) = z

toGrammar :: Stmt -> (Errors, G.Stmt)
toGrammar (Data' z tp vars cons abs p) = (es, G.Data z tp vars cons abs p')
                                    where
                                        (es,p') = toGrammar p
toGrammar (Var' z var tp Nothing p) = (es, G.Var z var tp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Inp' z inp tp p)      = (es, G.Inp z inp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Out' z out tp p)      = (es, G.Out z out tp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Evt' z int TypeB p)   = (es, G.Evt z int p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Func' z cod tp p)     = (es, G.Func z cod tp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (FuncI' z cod tp imp p) = (esi++es, G.FuncI z cod tp imp' p')
                                 where
                                   (es,p')    = toGrammar p
                                   (esi,imp') = toGrammar imp
toGrammar (Write z var exp)      = ([], G.Write z var exp)
toGrammar (AwaitInp z inp var)   = ([], G.AwaitInp z inp)
toGrammar (EmitExt z ext exp)    = ([], G.EmitExt z ext exp)
toGrammar (AwaitEvt z int var)   = ([], G.AwaitEvt z int)
toGrammar (EmitEvt z int val)    = ([], G.EmitEvt z int)
toGrammar (If z exp p1 p2)       = (es1++es2, G.If z exp p1' p2')
                                 where
                                   (es1,p1') = (toGrammar p1)
                                   (es2,p2') = (toGrammar p2)
toGrammar (Seq z p1 p2)          = (es1++es2, G.Seq z p1' p2') --seq z p1' p2')
                                 where
                                    (es1,p1') = (toGrammar p1)
                                    (es2,p2') = (toGrammar p2)
                                    --seq z1 (G.Seq z2 a b) p2' = G.Seq z1 a (seq z2 b p2')
                                    --seq z  p1'            p2' = G.Seq z p1' p2'
toGrammar (Loop z p)             = (es, G.Loop z p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Every z evt var p)    = (es, G.Every z evt p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Error z msg)          = ([], G.Error z msg)
toGrammar (Par' z p1 p2)         = (es1++es2, G.Par z p1' p2')
                                 where
                                   (es1,p1') = (toGrammar p1)
                                   (es2,p2') = (toGrammar p2)
toGrammar (Pause' z var p)       = (es, G.Pause z var p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Fin' z p)             = (es, G.Fin z p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Trap' z p)            = (es, G.Trap z p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Escape' z n)          = ([], G.Escape z n)
toGrammar (Clean' _ id p)        = (es'++es, p'')
                                 where
                                   (es, p')  = toGrammar p
                                   (es',p'') = clean id p'
toGrammar (Nop z)                = ([], G.Nop z)
toGrammar (Halt z)               = ([], G.Halt z)
toGrammar (RawS z vs)            = ([], G.RawS z vs)
toGrammar p                      = error $ "toGrammar: unexpected statement: " ++ (show p)
