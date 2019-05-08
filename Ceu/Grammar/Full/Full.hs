module Ceu.Grammar.Full.Full where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann        (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type       (Type(..))
import qualified Ceu.Grammar.Basic as B

-------------------------------------------------------------------------------

data Exp
    = Error  Ann Int            -- 1
    | Number Ann Int            -- 1
    | Cons   Ann ID_Data_Hier Exp  -- True
    | Read   Ann ID_Var         -- a ; xs
    | Arg    Ann
    | Unit   Ann                -- ()
    | Tuple  Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Func   Ann Type Stmt      -- function implementation
    | Call   Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

toBasicExp :: Exp -> B.Exp
toBasicExp (Error  z v)     = B.Error  z v
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
    getAnn (Error  z _)   = z
    getAnn (Number z _)   = z
    getAnn (Cons   z _ _) = z
    getAnn (Read   z _)   = z
    getAnn (Arg    z)     = z
    getAnn (Unit   z)     = z
    getAnn (Tuple  z _)   = z
    getAnn (Func   z _ _) = z
    getAnn (Call   z _ _) = z

-------------------------------------------------------------------------------

data Loc = LAny
         | LVar ID_Var
         | LUnit
         | LNumber Int
         | LCons ID_Data_Hier Loc
         | LTuple [Loc]
         | LExp Exp
  deriving (Eq, Show)

toBasicLoc LAny             = B.LAny
toBasicLoc (LVar   id)      = B.LVar id
toBasicLoc LUnit            = B.LUnit
toBasicLoc (LNumber n)      = B.LNumber n
toBasicLoc (LCons  tps loc) = B.LCons tps (toBasicLoc loc)
toBasicLoc (LTuple locs)    = B.LTuple $ map toBasicLoc locs
toBasicLoc (LExp   exp)     = B.LExp (toBasicExp exp)

-------------------------------------------------------------------------------

data Stmt
  = Class    Ann (ID_Class,[ID_Var]) [(ID_Class,[ID_Var])] Stmt -- new class declaration
  | Inst     Ann (ID_Class,[Type])   Stmt         -- new class instance
  | Data     Ann ID_Data_Hier [ID_Var] Type Bool  -- new type declaration
  | Var      Ann ID_Var Bool Type                 -- variable declaration
  | FuncS    Ann ID_Var Bool Type Stmt            -- function declaration
  | Match    Ann Loc Exp Stmt Stmt                -- match
  | Set      Ann Bool Loc Exp                     -- assignment statement
  | CallS    Ann Exp                              -- call function
  | If       Ann Exp Stmt Stmt                    -- conditional
  | Seq      Ann Stmt Stmt                        -- sequence
  | Loop     Ann Stmt                             -- infinite loop
  | Scope    Ann Stmt                             -- scope for local variables
  | Class'   Ann (ID_Class,[ID_Var]) [(ID_Class,[ID_Var])] Stmt Stmt -- new class declaration
  | Inst'    Ann (ID_Class,[Type]) Stmt Stmt      -- new class instance
  | Data'    Ann ID_Data_Hier [ID_Var] Type Bool Stmt -- new type declaration w/ stmts in scope
  | Var'     Ann ID_Var Bool Type Stmt            -- variable declaration w/ stmts in scope
  | Match'   Ann Bool Loc Exp Stmt Stmt           -- match w/ chk
  | Nop      Ann                                  -- nop as in basic Grammar
  | Ret      Ann Exp
  deriving (Eq, Show)

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class    z _ _ _) = z
    getAnn (Inst     z _ _)   = z
    getAnn (Data     z _ _ _ _) = z
    getAnn (Var      z _ _ _)   = z
    getAnn (FuncS    z _ _ _ _) = z
    getAnn (Seq      z _ _  ) = z
    getAnn (Loop     z _    ) = z
    getAnn (Scope    z _    ) = z
    getAnn (Data'    z _ _ _ _ _) = z
    getAnn (Var'     z _ _ _ _) = z
    getAnn (Match'   z _ _ _ _ _) = z
    getAnn (Nop      z      ) = z
    getAnn (Ret      z _    ) = z

toBasicStmt :: Stmt -> B.Stmt
toBasicStmt (Class' z me ext ifc p)       = B.Class z me ext (toBasicStmt ifc) (toBasicStmt p)
toBasicStmt (Inst'  z me imp p)           = B.Inst  z me     (toBasicStmt imp) (toBasicStmt p)
toBasicStmt (Data'  z tp vars flds abs p) = B.Data  z tp  vars flds abs (toBasicStmt p)
toBasicStmt (Var'   z var gen tp p)       = B.Var   z var gen tp (toBasicStmt p)
toBasicStmt (Match' z chk loc exp p1 p2)  = B.Match z chk (toBasicLoc loc) (toBasicExp exp)
                                                          (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (CallS  z e)                  = B.CallS z (toBasicExp e)
toBasicStmt (Seq    z p1 p2)              = B.Seq   z (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (Loop   z p)                  = B.Loop  z (toBasicStmt p)
toBasicStmt (Nop    z)                    = B.Nop   z
toBasicStmt (Ret    z exp)                = B.Ret   z (toBasicExp exp)
toBasicStmt p                             = error $ "toBasicStmt: unexpected statement: " ++ (show p)

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, Type->Type) -> Stmt -> Stmt
map_stmt f@(fs,_,_)  (Class z me ext p)       = fs (Class z me ext (map_stmt f p))
map_stmt f@(fs,_,_)  (Inst  z me p)           = fs (Inst  z me (map_stmt f p))
map_stmt f@(fs,_,ft) (Data  z me flds tp abs) = fs (Data  z me flds (ft tp) abs)
map_stmt f@(fs,_,ft) (Var   z id gen tp)      = fs (Var   z id gen (ft tp))
map_stmt f@(fs,_,ft) (FuncS z id gen tp p)    = fs (FuncS z id gen (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (Match z loc exp p1 p2)  = fs (Match z loc (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Set   z b loc exp)      = fs (Set   z b loc (map_exp f exp))
map_stmt f@(fs,_,_)  (CallS z exp)            = fs (CallS z (map_exp f exp))
map_stmt f@(fs,_,_)  (If    z exp p1 p2)      = fs (If    z (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Seq   z p1 p2)          = fs (Seq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Loop  z p)              = fs (Loop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (Scope z p)              = fs (Scope z (map_stmt f p))
map_stmt f@(fs,_,_)  (Ret   z exp)              = fs (Ret   z (map_exp f exp))
map_stmt f@(fs,_,_)  (Nop   z)                  = fs (Nop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, Type->Type) -> Exp -> Exp
map_exp f@(_,fe,_)  (Cons  z id e)  = fe (Cons  z id (map_exp f e))
map_exp f@(_,fe,_)  (Tuple z es)    = fe (Tuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (Func  z tp p)  = fe (Func  z (ft tp) (map_stmt f p))
map_exp f@(_,fe,_)  (Call  z e1 e2) = fe (Call  z (map_exp f e1) (map_exp f e2))
map_exp f@(_,fe,_)  exp             = fe exp
