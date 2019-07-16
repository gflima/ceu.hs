module Ceu.Grammar.Full.Full where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann               (Ann, HasAnn(..), annz)
import Ceu.Grammar.Constraints as Cs (Map)
import Ceu.Grammar.Type        as T  (TypeC)
import qualified Ceu.Grammar.Basic as B

-------------------------------------------------------------------------------

data Exp
    = EError Ann Int            -- 1
    | EVar   Ann ID_Var         -- a ; xs
    | EUnit  Ann                -- ()
    | ECons  Ann ID_Data_Hier   -- True
    | EField Ann ID_Data_Hier Int  -- List.Cons._1
    | EArg   Ann
    | ETuple Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc  Ann TypeC Stmt      -- function implementation
    | ECall  Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    | EAny   Ann
    | EExp   Ann Exp
    | EMatch Ann Exp Exp
    deriving (Eq, Show)

toBasicExp :: Exp -> B.Exp
toBasicExp (EError z v)     = B.EError z v
toBasicExp (EVar   z v)     = B.EVar   z v
toBasicExp (EUnit  z)       = B.EUnit  z
toBasicExp (ECons  z v)     = B.ECons  z v
toBasicExp (EField z f e)   = B.EField z f e
toBasicExp (EArg   z)       = B.EArg   z
toBasicExp (ETuple z es)    = B.ETuple z (map toBasicExp es)
toBasicExp (EFunc  z tp p)  = B.EFunc  z tp (toBasicStmt p)
toBasicExp (ECall  z e1 e2) = B.ECall  z (toBasicExp e1) (toBasicExp e2)
toBasicExp (EAny   z)       = B.EAny   z
toBasicExp (EExp   z e)     = B.EExp   z (toBasicExp e)
toBasicExp (EMatch z e p)   = B.EMatch z (toBasicExp e) (toBasicExp p)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (EError z _)   = z
    getAnn (ECons  z _)   = z
    getAnn (EField z _ _) = z
    getAnn (EVar   z _)   = z
    getAnn (EArg   z)     = z
    getAnn (EUnit  z)     = z
    getAnn (ETuple z _)   = z
    getAnn (EFunc  z _ _) = z
    getAnn (ECall  z _ _) = z

-------------------------------------------------------------------------------

data Stmt
  = Class    Ann ID_Class Cs.Map Stmt             -- new class declaration
  | Class'   Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] -- interface w/ body
  | Inst     Ann ID_Class TypeC Stmt              -- new class instance
  | Inst'    Ann ID_Class TypeC [(Ann,ID_Var,TypeC,Bool)] -- new class instance
  | Data     Ann TypeC Bool                       -- new type declaration
  | Var      Ann ID_Var TypeC                     -- variable declaration
  | FuncS    Ann ID_Var TypeC Stmt                -- function declaration
  | Match    Ann Bool Exp [(Stmt,Exp,Stmt)]       -- match
  | Match'   Ann Bool Exp [(Stmt,Exp,Stmt)]       -- match w/ chk
  | Set      Ann Bool Exp Exp                     -- assignment statement
  | CallS    Ann Exp                              -- call function
  | If       Ann Exp Stmt Stmt                    -- conditional
  | Seq      Ann Stmt Stmt                        -- sequence
  | Loop     Ann Stmt                             -- infinite loop
  | Scope    Ann Stmt                             -- scope for local variables
  | Nop      Ann                                  -- nop as in basic Grammar
  | Ret      Ann Exp
  -- declarations w/ scope
  | Class''  Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] Stmt
  | Inst''   Ann ID_Class TypeC  [(Ann,ID_Var,TypeC,Bool)] Stmt
  | Data''   Ann TypeC Bool Stmt
  | Var''    Ann ID_Var TypeC Stmt
  deriving (Eq, Show)

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class    z _ _ _)     = z
    getAnn (Inst     z _ _ _)     = z
    getAnn (Data     z _ _)       = z
    getAnn (Var      z _ _)       = z
    getAnn (FuncS    z _ _ _)     = z
    getAnn (Match'   z _ _ _)     = z
    getAnn (Seq      z _ _  )     = z
    getAnn (Loop     z _)         = z
    getAnn (Scope    z _)         = z
    getAnn (Nop      z)           = z
    getAnn (Ret      z _)         = z
    getAnn (Data''   z _ _ _)     = z
    getAnn (Var''    z _ _ _)     = z

toBasicStmt :: Stmt -> B.Stmt
toBasicStmt (Class'' z id  cs ifc p) = B.Class z id  cs ifc (toBasicStmt p)
toBasicStmt (Inst''  z cls tp imp p) = B.Inst  z cls tp imp (toBasicStmt p)
toBasicStmt (Data''  z tp abs p)     = B.Data  z tp abs (toBasicStmt p)
toBasicStmt (Var''   z var tp p)     = B.Var   z var tp (toBasicStmt p)
toBasicStmt (Match'  z chk exp cses) = B.Match z chk (toBasicExp exp)
                                         (map (\(ds,pt,st) -> (toBasicStmt ds, toBasicExp pt, toBasicStmt st)) cses)
toBasicStmt (CallS   z e)            = B.CallS z (toBasicExp e)
toBasicStmt (Seq     z p1 p2)        = B.Seq   z (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (Loop    z p)            = B.Loop  z (toBasicStmt p)
toBasicStmt (Nop     z)              = B.Nop   z
toBasicStmt (Ret     z exp)          = B.Ret   z (toBasicExp exp)
toBasicStmt p                        = error $ "toBasicStmt: unexpected statement: " ++ (show p)

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Stmt -> Stmt
map_stmt f@(fs,_,_)  (Class z id  cs p)  = fs (Class z id  cs (map_stmt f p))
map_stmt f@(fs,_,ft) (Inst  z cls tp p)  = fs (Inst  z cls (ft tp) (map_stmt f p))
map_stmt f@(fs,_,ft) (Data  z tp abs)    = fs (Data  z (ft tp) abs)
map_stmt f@(fs,_,ft) (Var   z id tp)     = fs (Var   z id (ft tp))
map_stmt f@(fs,_,ft) (FuncS z id tp p)   = fs (FuncS z id (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (Match z chk exp cses) = fs (Match z chk (map_exp f exp)
                                                (map (\(ds,pt,st) -> (map_stmt f ds, map_exp f pt, map_stmt f st)) cses))
map_stmt f@(fs,_,_)  (Set   z b loc exp) = fs (Set   z b loc (map_exp f exp))
map_stmt f@(fs,_,_)  (CallS z exp)       = fs (CallS z (map_exp f exp))
map_stmt f@(fs,_,_)  (If    z exp p1 p2) = fs (If    z (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Seq   z p1 p2)     = fs (Seq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Loop  z p)         = fs (Loop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (Scope z p)         = fs (Scope z (map_stmt f p))
map_stmt f@(fs,_,_)  (Ret   z exp)       = fs (Ret   z (map_exp f exp))
map_stmt f@(fs,_,_)  (Nop   z)           = fs (Nop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Exp -> Exp
map_exp f@(_,fe,_)  (ECons  z id)    = fe (ECons  z id)
map_exp f@(_,fe,_)  (ETuple z es)    = fe (ETuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (EFunc  z tp p)  = fe (EFunc  z (ft tp) (map_stmt f p))
map_exp f@(_,fe,_)  (ECall  z e1 e2) = fe (ECall  z (map_exp f e1) (map_exp f e2))
map_exp f@(_,fe,_)  exp              = fe exp
