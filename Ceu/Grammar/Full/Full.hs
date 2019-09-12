module Ceu.Grammar.Full.Full where

import Debug.Trace
import Data.List                     (intercalate)

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann               (Ann, HasAnn(..), annz)
import Ceu.Grammar.Constraints as Cs (Map)
import Ceu.Grammar.Type        as T  (Type(..), TypeC, FuncType, hier2str, show', showC)
import qualified Ceu.Grammar.Basic as B

-------------------------------------------------------------------------------

data Exp
    = EError Ann Int            -- 1
    | EVar   Ann ID_Var         -- a ; xs
    | ERef   Ann Exp            -- ref a
    | EUnit  Ann                -- ()
    | ECons  Ann ID_Data_Hier   -- True
    | EField Ann ID_Data_Hier String -- List.Cons._1 / Student.age
    | EArg   Ann
    | ETuple Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc  Ann TypeC Exp Stmt -- function implementation
    | EFunc' Ann TypeC     Stmt
    | ECall  Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    | EAny   Ann
    | EExp   Ann Exp
    | EMatch Ann Exp Exp
    deriving (Eq, Show)

toBasicExp :: Exp -> B.Exp
toBasicExp (EError z v)     = B.EError z v
toBasicExp (EVar   z v)     = B.EVar   z v
toBasicExp (ERef   z e)     = B.ERefRef z (toBasicExp e)
toBasicExp (EUnit  z)       = B.EUnit  z
toBasicExp (ECons  z v)     = B.ECons  z v
toBasicExp (EField z f e)   = B.EField z f e
toBasicExp (EArg   z)       = B.EArg   z
toBasicExp (ETuple z es)    = B.ETuple z (map toBasicExp es)
toBasicExp (EFunc' z tp p)  = B.EFunc  z tp (B.EUnit z) (toBasicStmt p)
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
    getAnn (EFunc' z _ _) = z
    getAnn (ECall  z _ _) = z

-------------------------------------------------------------------------------

data Stmt
  = SClass    Ann ID_Class Cs.Map Stmt             -- new class declaration
  | SClass'   Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] -- interface w/ body
  | SInst     Ann ID_Class TypeC Stmt              -- new class instance
  | SInst'    Ann ID_Class TypeC [(Ann,ID_Var,TypeC,Bool)] -- new class instance
  | SData     Ann Type (Maybe [ID_Var]) Type Cs.Map Bool      -- new type declaration
  | SVar      Ann ID_Var TypeC (Maybe Exp)         -- (z id tp ini)   -- variable declaration
  | SFunc     Ann ID_Var TypeC Exp Stmt            -- function declaration
  | SMatch    Ann Bool Bool Exp [(Stmt,Exp,Stmt)]  -- match
  | SSet      Ann Bool Bool Exp Exp                -- assignment statement
  | SCall     Ann Exp                              -- call function
  | SIf       Ann Exp Stmt Stmt                    -- conditional
  | SSeq      Ann Stmt Stmt                        -- sequence
  | SLoop     Ann Stmt                             -- infinite loop
  | SScope    Ann Stmt                             -- scope for local variables
  | SNop      Ann                                  -- nop as in basic Grammar
  | SRet      Ann Exp
  -- declarations w/ scope
  | SClass''  Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] Stmt
  | SInst''   Ann ID_Class TypeC  [(Ann,ID_Var,TypeC,Bool)] Stmt
  | SData''   Ann Type (Maybe [ID_Var]) Type Cs.Map Bool Stmt
  | SVar''    Ann ID_Var TypeC (Maybe Exp) Stmt
  deriving (Eq, Show)

sSeq a b = SSeq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (SClass    z _ _ _)     = z
    getAnn (SInst     z _ _ _)     = z
    getAnn (SData     z _ _ _ _ _) = z
    getAnn (SVar      z _ _ _)     = z
    getAnn (SFunc     z _ _ _ _)   = z
    getAnn (SSeq      z _ _  )     = z
    getAnn (SLoop     z _)         = z
    getAnn (SScope    z _)         = z
    getAnn (SNop      z)           = z
    getAnn (SRet      z _)         = z
    getAnn (SData''   z _ _ _ _ _ _) = z
    getAnn (SVar''    z _ _ _ _)   = z

toBasicStmt :: Stmt -> B.Stmt
toBasicStmt (SClass'' z id  cs ifc p) = B.SClass z id  cs ifc (toBasicStmt p)
toBasicStmt (SInst''  z cls tp imp p) = B.SInst  z cls tp imp (toBasicStmt p)
toBasicStmt (SData''  z tp nms st cs abs p) = B.SData z tp nms st cs abs (toBasicStmt p)
toBasicStmt (SVar''   z var tp Nothing p) = B.SVar   z var tp (toBasicStmt p)
toBasicStmt (SMatch   z ini chk exp cses) = B.SMatch z ini chk (toBasicExp exp)
                                              (map (\(ds,pt,st) -> (toBasicStmt ds, toBasicExp pt, toBasicStmt st)) cses)
toBasicStmt (SCall   z e)             = B.SCall z (toBasicExp e)
toBasicStmt (SSeq     z p1 p2)        = B.SSeq   z (toBasicStmt p1) (toBasicStmt p2)
toBasicStmt (SLoop    z p)            = B.SLoop  z (toBasicStmt p)
toBasicStmt (SNop     z)              = B.SNop   z
toBasicStmt (SRet     z exp)          = B.SRet   z (toBasicExp exp)
toBasicStmt p                         = error $ "toBasicStmt: unexpected statement: " ++ (show p)

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Stmt -> Stmt
map_stmt f@(fs,_,_)  (SClass z id  cs p)            = fs (SClass   z id  cs (map_stmt f p))
map_stmt f@(fs,_,_)  (SClass' z id cs ifc)          = fs (SClass'  z id cs ifc)
map_stmt f@(fs,_,_)  (SClass'' z id cs ifc p)       = fs (SClass'' z id cs ifc (map_stmt f p))
map_stmt f@(fs,_,ft) (SInst  z cls tp p)            = fs (SInst    z cls (ft tp) (map_stmt f p))
map_stmt f@(fs,_,ft) (SInst' z cls tp ifc)          = fs (SInst'   z cls (ft tp) ifc)
map_stmt f@(fs,_,ft) (SInst'' z cls tp ifc p)       = fs (SInst''  z cls (ft tp) ifc (map_stmt f p))
map_stmt f@(fs,_,ft) (SData  z tp nms st cs abs)    = fs (SData    z tp nms st cs abs)
map_stmt f@(fs,_,ft) (SData'' z tp nms st cs abs p) = fs (SData''  z tp nms st cs abs (map_stmt f p))
map_stmt f@(fs,_,ft) (SVar   z id tp ini)           = fs (SVar     z id (ft tp) (fmap (map_exp f) ini))
map_stmt f@(fs,_,ft) (SVar'' z id tp ini p)         = fs (SVar''   z id (ft tp) (fmap (map_exp f) ini) (map_stmt f p))
map_stmt f@(fs,_,ft) (SFunc  z id tp ps bd)         = fs (SFunc    z id (ft tp) (map_exp f ps) (map_stmt f bd))
map_stmt f@(fs,_,_)  (SMatch z ini chk exp cses)    = fs (SMatch   z ini chk (map_exp f exp)
                                                        (map (\(ds,pt,st) -> (map_stmt f ds, map_exp f pt, map_stmt f st)) cses))
map_stmt f@(fs,_,_)  (SSet   z ini b loc exp) = fs (SSet   z ini b loc (map_exp f exp))
map_stmt f@(fs,_,_)  (SCall  z exp)           = fs (SCall  z (map_exp f exp))
map_stmt f@(fs,_,_)  (SIf    z exp p1 p2)     = fs (SIf    z (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (SSeq   z p1 p2)         = fs (SSeq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (SLoop  z p)             = fs (SLoop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (SScope z p)             = fs (SScope z (map_stmt f p))
map_stmt f@(fs,_,_)  (SRet   z exp)           = fs (SRet   z (map_exp f exp))
map_stmt f@(fs,_,_)  (SNop   z)               = fs (SNop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Exp -> Exp
map_exp f@(_,fe,_)  (ECons  z id)       = fe (ECons  z id)
map_exp f@(_,fe,_)  (ETuple z es)       = fe (ETuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (EFunc  z tp ps bd) = fe (EFunc  z (ft tp) (map_exp f ps) (map_stmt f bd))
map_exp f@(_,fe,ft) (EFunc' z tp bd)    = fe (EFunc' z (ft tp) (map_stmt f bd))
map_exp f@(_,fe,_)  (ECall  z e1 e2)    = fe (ECall  z (map_exp f e1) (map_exp f e2))
map_exp f@(_,fe,_)  exp                 = fe exp

-------------------------------------------------------------------------------

traceStmt :: Stmt -> Stmt
traceStmt s = traceShow (show_stmt 0 s) s

rep spc = replicate spc ' '

show_stmt :: Int -> Stmt -> String
show_stmt spc (SSeq _ p1 p2)              = show_stmt spc p1 ++ "\n" ++ show_stmt spc p2
show_stmt spc (SClass'  _ id _ _)         = rep spc ++ "constraint " ++ id
show_stmt spc (SClass'' _ id _ _ p)       = rep spc ++ "constraint " ++ id ++ "\n" ++ show_stmt spc p
show_stmt spc (SInst'  _ id _ _)          = rep spc ++ "instance " ++ id
show_stmt spc (SData   _ (TData False id _) _ tp _ _  ) = rep spc ++ "data " ++ intercalate "." id ++ T.show' tp
show_stmt spc (SData'' _ (TData False id _) _ tp _ _ p) = rep spc ++ "data " ++ intercalate "." id ++ T.show' tp ++ "\n" ++ show_stmt spc p
show_stmt spc (SVar _ id tpc Nothing)  = rep spc ++ "var " ++ id ++ ": " ++ T.showC tpc
show_stmt spc (SVar _ id tpc (Just e)) = rep spc ++ "var " ++ id ++ ": " ++ T.showC tpc ++ " = " ++ show_exp spc e
show_stmt spc (SVar'' _ id tpc Nothing  p) = rep spc ++ "var " ++ id ++ ": " ++ T.showC tpc ++ "\n" ++ show_stmt spc p
--show_stmt spc (SVar'' _ id tpc (Just e) p) = rep spc ++ "var " ++ id ++ ": " ++ T.showC tpc ++ " = " ++ show_exp spc e ++ "\n" ++ show_stmt spc p
show_stmt spc (SIf  _ e t f)              = rep spc ++ "if " ++ show_exp spc e ++ "then\n" ++
                                                          show_stmt (spc+2) t ++ "\n" ++
                                            rep spc ++ "else\n" ++
                                                          show_stmt (spc+2) f ++ "\n"
show_stmt spc (SMatch _ True _ exp [(SNop _,var,p)]) = rep spc ++ "init " ++ show_exp spc var ++ " = " ++ show_exp spc exp ++ "\n" ++ show_stmt spc p
show_stmt spc (SMatch _ _ _ exp cses)  = rep spc ++ "match " ++ show_exp spc exp ++ " with\n" ++ (concatMap f cses)
                                         where
                                          f (ds,pt,st) = rep (spc+4) ++ show_exp (spc+4) pt ++
                                                          " { " ++ show_stmt 0 ds ++ " } then\n" ++
                                                          show_stmt (spc+8) st ++ "\n"
show_stmt spc (SRet _ e)                  = rep spc ++ "return " ++ show_exp spc e
show_stmt spc (SNop _)                    = rep spc ++ "nop"
{-
show_stmt spc (SCall _ e)              = rep spc ++ "call " ++ show_exp spc e
show_stmt spc (SMatch _ _ False exp [(_,pt,st)])
                                       = rep spc ++ "set " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
show_stmt spc (SMatch _ _ True  exp ((ds,pt,st):_))
                                       = rep spc ++ "set! " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
-}
show_stmt _ p = error $ show p

show_exp :: Int -> Exp -> String
show_exp spc (EVar   _ id)        = id
show_exp spc (ETuple _ es)        = "(" ++ intercalate "," (map (show_exp spc) es) ++ ")"
show_exp spc (ECons  _ ["Int",n]) = n
show_exp spc (ECons  _ id)        = hier2str id
show_exp spc (EField _ id fld)    = hier2str id ++ "." ++ fld
show_exp spc (EFunc  _ _ ps p)    = "func " ++ show_exp spc ps ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (EFunc' _ _    p)    = "func " ++                    "\n" ++ show_stmt (spc+4) p
show_exp spc (ECall  _ e1 e2)     = "call" ++ " " ++ show_exp spc e1 ++ " " ++ show_exp spc e2
show_exp spc (EMatch _ exp pat)   = "match" ++ " " ++ show_exp spc exp ++ " with " ++ show_exp spc pat
show_exp spc (EExp   _ exp)       = show_exp spc exp
show_exp spc (EArg   _)           = "arg"
show_exp spc (EAny   _)           = "_"
{-
show_exp spc (EUnit  _)           = "()"
show_exp spc (EError _ n)         = "error " ++ show n
show_exp spc (EUpv   _)           = "upv"
show_exp spc (EFunc  _ _ _ p)     = "func" ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (ERefRef _ exp)      = "ref " ++ show_exp spc exp
show_exp spc (ERefIni _ exp)      = show_exp spc exp
show_exp spc (ERefDer _ exp)      = "acc " ++ show_exp spc exp
-}
show_exp _ e = error $ show e
