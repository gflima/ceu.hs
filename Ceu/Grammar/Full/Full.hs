module Ceu.Grammar.Full.Full where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann        (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type       (Type(..))
import qualified Ceu.Grammar.Basic as B

-------------------------------------------------------------------------------

data Exp
    = Number Ann Int            -- 1
    | Cons   Ann [ID_Type] Exp  -- True
    | Read   Ann ID_Var         -- a ; xs
    | Arg    Ann
    | Unit   Ann                -- ()
    | Tuple  Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Func   Ann Type Stmt      -- function implementation
    | Call   Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

toBasicExp :: Exp -> B.Exp
toBasicExp (Number z v)     = B.Number z v
toBasicExp (Cons   z v e)   = B.Cons   z v (toBasicExp e)
toBasicExp (Read   z v)     = B.Read   z v
toBasicExp (Arg    z)       = B.Arg    z
toBasicExp (Unit   z)       = B.Unit   z
toBasicExp (Tuple  z es)    = B.Tuple  z (map toBasicExp es)
toBasicExp (Func   z tp p)  = B.Func   z tp (toBasicStmt p)
toBasicExp (Call   z e1 e2) = B.Call   z (toBasicExp e1) (toBasicExp e2)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (Number z _)   = z
    getAnn (Cons   z _ _) = z
    getAnn (Read   z _)   = z
    getAnn (Arg    z)     = z
    getAnn (Unit   z)     = z
    getAnn (Tuple  z _)   = z
    getAnn (Func   z _ _) = z
    getAnn (Call   z _ _) = z

-------------------------------------------------------------------------------

data Stmt
  = Class    Ann ID_Class [ID_Var] Stmt           -- new class declaration
  | Inst     Ann ID_Class [Type]   Stmt           -- new class instance
  | Data     Ann [ID_Type] [ID_Var] Type Bool     -- new type declaration
  | Var      Ann ID_Var Type                      -- variable declaration
  | FuncS    Ann ID_Var Type Stmt                 -- function declaration
  | Write    Ann Loc Exp                          -- assignment statement
  | CallS    Ann Exp Exp                          -- call function
  | If       Ann Exp Stmt Stmt                    -- conditional
  | Seq      Ann Stmt Stmt                        -- sequence
  | Loop     Ann Stmt                             -- infinite loop
  | Scope    Ann Stmt                             -- scope for local variables
  | Class'   Ann ID_Class [ID_Var] Stmt Stmt      -- new class declaration
  | Inst'    Ann ID_Class [Type]   Stmt Stmt      -- new class instance
  | Data'    Ann [ID_Type] [ID_Var] Type Bool Stmt -- new type declaration w/ stmts in scope
  | Var'     Ann ID_Var Type Stmt                 -- variable declaration w/ stmts in scope
  | Nop      Ann                                  -- nop as in basic Grammar
  | Ret      Ann Exp
  deriving (Eq, Show)

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class    z _ _ _) = z
    getAnn (Inst     z _ _ _) = z
    getAnn (Data     z _ _ _ _) = z
    getAnn (Var      z _ _)   = z
    getAnn (FuncS    z _ _ _) = z
    getAnn (Write    z _ _  ) = z
    getAnn (If       z _ _ _) = z
    getAnn (Seq      z _ _  ) = z
    getAnn (Loop     z _    ) = z
    getAnn (Scope    z _    ) = z
    getAnn (Data'    z _ _ _ _ _) = z
    getAnn (Var'     z _ _ _) = z
    getAnn (Nop      z      ) = z
    getAnn (Ret      z _    ) = z

toBasicStmt :: Stmt -> B.Stmt
toBasicStmt (Class' z cls vars ifc p)    = B.Class z cls vars (toBasicStmt ifc) (toBasicStmt p)
toBasicStmt (Inst'  z cls tps  imp p)    = B.Inst  z cls tps  (toBasicStmt imp) (toBasicStmt p)
toBasicStmt (Data' z tp vars flds abs p) = B.Data  z tp  vars flds abs (toBasicStmt p)
toBasicStmt (Var' z var tp p)  = B.Var z var tp (toBasicStmt p)
toBasicStmt (Write z loc exp)  = B.Write z loc (toBasicExp exp)
toBasicStmt (If z exp p1 p2)   = B.If z (toBasicExp exp) (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (Seq z p1 p2)      = B.Seq z (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (Loop z p)         = B.Loop z (toBasicStmt p)
toBasicStmt (Nop z)            = B.Nop z
toBasicStmt (Ret z exp)        = B.Ret z (toBasicExp exp)
toBasicStmt p                  = error $ "toBasicStmt: unexpected statement: " ++ (show p)
