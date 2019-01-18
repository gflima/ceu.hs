module Ceu.Grammar.Full.Full where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann        (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type       (Type(..))
import qualified Ceu.Grammar.Basic as B

-- Special events:
-- "BOOT"
-- "ASYNC"

-- Program (pg 5).
data Stmt
  = Data     Ann ID_Type [ID_Var] [DataCons] Bool -- new type declaration
  | Var      Ann ID_Var Type                    -- variable declaration
  | Write    Ann Loc B.Exp                      -- assignment statement
  | CallS    Ann B.Exp B.Exp                    -- call function
  | If       Ann B.Exp Stmt Stmt                -- conditional
  | Seq      Ann Stmt Stmt                      -- sequence
  | Loop     Ann Stmt                           -- infinite loop
  | Scope    Ann Stmt                           -- scope for local variables
  | Data'    Ann ID_Type [ID_Var] [DataCons] Bool Stmt -- new type declaration w/ stmts in scope
  | Var'     Ann ID_Var Type Stmt               -- variable declaration w/ stmts in scope
  | Nop      Ann                                -- nop as in basic Grammar
  | Ret      Ann B.Exp
  deriving (Eq, Show)

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Data     z _ _ _ _) = z
    getAnn (Var      z _ _)   = z
    getAnn (Write    z _ _  ) = z
    getAnn (If       z _ _ _) = z
    getAnn (Seq      z _ _  ) = z
    getAnn (Loop     z _    ) = z
    getAnn (Scope    z _    ) = z
    getAnn (Data'    z _ _ _ _ _) = z
    getAnn (Var'     z _ _ _) = z
    getAnn (Nop      z      ) = z
    getAnn (Ret      z _    ) = z

toBasic :: Stmt -> (Errors, B.Stmt)
toBasic (Data' z tp vars cons abs p) = (es, B.Data z tp vars cons abs p')
                                       where
                                        (es,p') = toBasic p
toBasic (Var' z var tp p)      = (es, B.Var z var tp p')
                                 where
                                   (es,p') = toBasic p
toBasic (Write z var exp)      = ([], B.Write z var exp)
toBasic (If z exp p1 p2)       = (es1++es2, B.If z exp p1' p2')
                                 where
                                   (es1,p1') = (toBasic p1)
                                   (es2,p2') = (toBasic p2)
toBasic (Seq z p1 p2)          = (es1++es2, B.Seq z p1' p2') --seq z p1' p2')
                                 where
                                    (es1,p1') = (toBasic p1)
                                    (es2,p2') = (toBasic p2)
                                    --seq z1 (B.Seq z2 a b) p2' = B.Seq z1 a (seq z2 b p2')
                                    --seq z  p1'            p2' = B.Seq z p1' p2'
toBasic (Loop z p)             = (es, B.Loop z p')
                                 where
                                   (es,p') = toBasic p
toBasic (Nop z)                = ([], B.Nop z)
toBasic (Ret z exp)            = ([], B.Ret z exp)
toBasic p                      = error $ "toBasic: unexpected statement: " ++ (show p)
