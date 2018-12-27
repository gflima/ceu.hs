module Ceu.Grammar.Full.Grammar where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp (Exp(..), RawAt)
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval as E
import Ceu.Grammar.Full.Clean
import Debug.Trace

-- Special events:
-- "BOOT"
-- "ASYNC"

type In = (ID_Inp, Maybe Val)

type Fin ann = (Stmt ann, Stmt ann, Stmt ann)

-- Program (pg 5).
data Stmt ann
  = Var      ann ID_Var Type (Maybe (Fin ann))  -- variable declaration
  | Inp      ann ID_Inp Bool                         -- output declaration
  | Out      ann ID_Out Bool                         -- output declaration
  | Evt      ann ID_Evt Bool                         -- event declaration
  | CodI     ann ID_Var Type Type                    -- code/inst declaration
  | Write    ann ID_Var (Exp ann)                    -- assignment statement
  | AwaitInp ann ID_Inp (Maybe ID_Var)               -- await external event
  | EmitExt  ann ID_Ext (Maybe (Exp ann))            -- emit external event
  | AwaitTmr ann (Exp ann)                           -- await timer
  | AwaitEvt ann ID_Evt (Maybe ID_Var)               -- await internal event
  | EmitEvt  ann ID_Evt (Maybe (Exp ann))            -- emit internal event
  | Break    ann                                     -- loop escape
  | If       ann (Exp ann) (Stmt ann) (Stmt ann)     -- conditional
  | Seq      ann (Stmt ann) (Stmt ann)               -- sequence
  | Loop     ann (Stmt ann)                          -- infinite loop
  | Every    ann ID (Maybe ID_Var) (Stmt ann)        -- event iteration
  | And      ann (Stmt ann) (Stmt ann)               -- par/and statement
  | Or       ann (Stmt ann) (Stmt ann)               -- par/or statement
  | Par      ann (Stmt ann) (Stmt ann)               -- par statement
  | Spawn    ann (Stmt ann)                          -- spawn statement
  | Pause    ann ID (Stmt ann)                       -- pause/suspend statement
  | Fin      ann (Stmt ann) (Stmt ann) (Stmt ann)    -- finalize/pause/resume statement
  | Async    ann (Stmt ann)                          -- async statement
  | Trap     ann (Maybe ID_Var) (Stmt ann)           -- trap with optional assignment
  | Escape   ann (Maybe ID_Var) (Maybe (Exp ann))    -- escape enclosing trap
  | Scope    ann (Stmt ann)                          -- scope for local variables
  | Error    ann String                              -- generate runtime error (for testing purposes)
  | Var'     ann ID_Var Type (Maybe (Fin ann)) (Stmt ann) -- variable declaration w/ stmts in scope
  | Inp'     ann ID_Inp Bool (Stmt ann)              -- output declaration w/ stmts in scope
  | Out'     ann ID_Out Bool (Stmt ann)              -- output declaration w/ stmts in scope
  | Evt'     ann ID_Evt Bool (Stmt ann)              -- event declaration w/ stmts in scope
  | CodI'    ann ID_Cod Type Type (Stmt ann)         -- event declaration w/ stmts in scope
  | Or'      ann (Stmt ann) (Stmt ann)               -- used as an Or with possibly non-terminating trails
  | Par'     ann (Stmt ann) (Stmt ann)               -- par as in basic Grammar
  | Pause'   ann ID_Var (Stmt ann)                   -- pause as in basic Grammar
  | Fin'     ann (Stmt ann)                          -- fin as in basic Grammar
  | Trap'    ann (Stmt ann)                          -- trap as in basic Grammar
  | Escape'  ann Int                                 -- escape as in basic Grammar
  | Clean'   ann String (Stmt ann)                   -- temporary statement
  | Nop      ann                                     -- nop as in basic Grammar
  | Halt     ann                                     -- halt as in basic Grammar
  | RawS     ann [RawAt ann]                         -- raw as in basic Grammar
  deriving (Eq, Show)

sSeq a b = Seq () a b
sPar a b = Par () a b
sAnd a b = And () a b
sOr  a b = Or  () a b

infixr 1 `sSeq`
infixr 0 `sAnd`
infixr 0 `sOr`

getAnn :: Stmt ann -> ann
getAnn (Var      z _ _ _) = z
getAnn (Inp      z _ _  ) = z
getAnn (Out      z _ _  ) = z
getAnn (Evt      z _ _  ) = z
getAnn (CodI     z _ _ _) = z
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
getAnn (Var'     z _ _ _ _) = z
getAnn (Inp'     z _ _ _) = z
getAnn (Out'     z _ _ _) = z
getAnn (Evt'     z _ _ _) = z
getAnn (CodI'    z _ _ _ _) = z
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

toGrammar :: (Eq ann, Ann ann) => (Stmt ann) -> (Errors, G.Stmt ann)
toGrammar (Var' z var tp Nothing p) = (es, G.Var z var tp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Inp' z inp b p)       = (es, G.Inp z inp p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Out' z out b p)       = (es, G.Out z out p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (Evt' z int b p)       = (es, G.Evt z int p')
                                 where
                                   (es,p') = toGrammar p
toGrammar (CodI' z cod inp out p) = (es, G.CodI z cod inp out p')
                                 where
                                   (es,p') = toGrammar p
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
toGrammar p                      = error $ "toGrammar: unexpected statement: " -- ++(show p)

-------------------------------------------------------------------------------

stmt2word :: (Stmt ann) -> String
stmt2word stmt = case stmt of
  Var _ _ _ _    -> "declaration"
  Inp _ _ _      -> "declaration"
  Out _ _ _      -> "declaration"
  Evt _ _ _      -> "declaration"
  CodI _ _ _ _   -> "declaration"
  Write _ _ _    -> "assignment"
  AwaitInp _ _ _ -> "await"
  AwaitTmr _ _   -> "await"
  EmitExt _ _ _  -> "emit"
  AwaitEvt _ _ _ -> "await"
  EmitEvt _ _ _  -> "emit"
  Break _        -> "break"
  If _ _ _ _     -> "if"
  Seq _ _ _      -> "sequence"
  Loop _ _       -> "loop"
  Every _ _ _ _  -> "every"
  And _ _ _      -> "par/and"
  Or _ _ _       -> "par/or"
  Spawn _ _      -> "spawn"
  Pause _ _ _    -> "pause/if"
  Fin _ _ _ _    -> "finalize"
  Async _ _      -> "async"
  Trap _ _ _     -> "trap"
  Escape _ _ _   -> "escape"
  Scope _ _      -> "scope"
  Error _ _      -> "error"
  Var' _ _ _ _ _ -> "declaration"
  Inp' _ _ _ _   -> "declaration"
  Out' _ _ _ _   -> "declaration"
  Evt' _ _ _ _   -> "declaration"
  CodI' _ _ _ _ _ -> "declaration"
  Par' _ _ _     -> "parallel"
  Pause' _ _ _   -> "pause/if"
  Fin' _ _       -> "finalize"
  Trap' _ _      -> "trap"
  Escape' _ _    -> "escape"
  Clean' _ _ _   -> "clean"
  Nop _          -> "nop"
  Halt _         -> "halt"
  RawS _ _       -> "raw"

instance (Ann ann) => INode (Stmt ann) where
  toWord   = stmt2word
  toSource = getSource . getAnn
  toN      = getN . getAnn
  toTrails = getTrails . getAnn
