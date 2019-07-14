module Ceu.Grammar.Basic where

import Data.Bool                      (bool)
import Data.List                      (intercalate)

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann                (Ann, HasAnn(..), annz)
import Ceu.Grammar.Constraints as Cs  (Map, cz)
import Ceu.Grammar.Type        as T   (TypeC, Type(..), show', hier2str)

-------------------------------------------------------------------------------

data Exp
    = EError Ann Int
    | EVar   Ann ID_Var         -- a ; xs
    | EUnit  Ann                -- ()
    | ECons  Ann ID_Data_Hier   -- Bool.True ; Int.1 ; Tree.Node
    | ETuple Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc  Ann TypeC Stmt     -- function implementation
    | ECall  Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    | EAny   Ann
    | EArg   Ann
    | EExp   Ann Exp
    | EMatch Ann Exp Exp
    deriving (Eq, Show)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (EError z _)   = z
    getAnn (EVar   z _)   = z
    getAnn (EUnit  z)     = z
    getAnn (ECons  z _)   = z
    getAnn (ETuple z _)   = z
    getAnn (EFunc  z _ _) = z
    getAnn (ECall  z _ _) = z
    getAnn (EAny   z)     = z
    getAnn (EArg   z)     = z
    getAnn (EExp   z _)   = z
    getAnn (EMatch z _ _) = z

-------------------------------------------------------------------------------

data Stmt
    = Class  Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class declaration
    | Inst   Ann ID_Class TypeC  [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class instance
    | Data   Ann TypeC Bool Stmt              -- new type declaration
    | Var    Ann ID_Var TypeC Stmt            -- variable declaration
    | Match  Ann Bool Exp [(Stmt,Exp,Stmt)]   -- match/assignment/if statement
    | CallS  Ann Exp                          -- call function
    | Seq    Ann Stmt Stmt                    -- sequence
    | Loop   Ann Stmt                         -- infinite loop
    | Ret    Ann Exp                          -- terminate program with Ret
    | Nop    Ann                              -- dummy statement (internal)
    deriving (Eq, Show)

-------------------------------------------------------------------------------

isClass id1 (Class _ id2 _ _ _) = (id1 == id2)
isClass _   _                   = False

isData  hr1 (Data  _ (TData hr2 _ _,_) _ _) = (hr1' == hier2str hr2) where
                                                hr1' = bool hr1 "Int" (take 4 hr1 == "Int.")
isData  _   _                               = False

isVar   id1 (Var   _ id2 _ _)   = (id1 == id2)
isVar   _   _                   = False

-------------------------------------------------------------------------------

rep spc = replicate spc ' '

show_stmt :: Int -> Stmt -> String
--show_stmt spc (Class _ (id,_) _ _ p) = rep spc ++ "class "  ++ id ++ "\n" ++ show_stmt spc p
--show_stmt spc (Inst  _ (id,_) _ p)   = rep spc ++ "inst "   ++ id ++ "\n" ++ show_stmt spc p
show_stmt spc (Data _ (TData id _ _,_) _ p) = rep spc ++ "data "   ++ intercalate "." id ++ "\n" ++ show_stmt spc p
show_stmt spc (Var _ id (tp,_) p)     = rep spc ++ "var "    ++ id ++ ": " ++ T.show' tp ++ "\n" ++ show_stmt spc p
show_stmt spc (CallS _ e)             = rep spc ++ "call " ++ show_exp spc e
show_stmt spc (Ret _ e)               = rep spc ++ "return " ++ show_exp spc e
show_stmt spc (Seq _ p1 p2)           = show_stmt spc p1 ++ "\n" ++ show_stmt spc p2
  --rep spc ++ "--\n" ++ show_stmt (spc+4) p1 ++ rep spc ++ "--\n" ++ show_stmt (spc+4) p2
show_stmt spc (Match _ False exp [(_,pt,st)])
                                      = rep spc ++ "set " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
show_stmt spc (Match _ True  exp ((ds,pt,st):_))
                                      = rep spc ++ "set! " ++ show_exp spc pt ++ " = " ++
                                          show_exp spc exp ++ "\n" ++ show_stmt spc st
show_stmt spc (Match _ chk exp cses)  = rep spc ++ "match " ++ show_exp spc exp ++ " with\n" ++ (concatMap f cses)
                                        where
                                          f (ds,pt,st) = rep (spc+4) ++ show_exp (spc+4) pt ++
                                                          " { " ++ show_stmt 0 ds ++ " } then\n" ++
                                                          show_stmt (spc+8) st ++ "\n"
show_stmt spc (Nop _)                 = rep spc ++ "nop"
show_stmt spc p = error $ show p

show_exp :: Int -> Exp -> String
show_exp spc (EAny   _)           = "_"
show_exp spc (EError _ n)         = "error " ++ show n
show_exp spc (ECons  _ ["Int",n]) = n
show_exp spc (ECons  _ id)        = hier2str id
show_exp spc (EVar   _ id)        = id
show_exp spc (EArg   _)           = "arg"
show_exp spc (ETuple _ es)        = "(" ++ intercalate "," (map (show_exp spc) es) ++ ")"
show_exp spc (EFunc  _ _ p)       = "func" ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (ECall  _ e1 e2)     = "call" ++ " " ++ show_exp spc e1 ++ " " ++ show_exp spc e2
show_exp spc (EMatch _ exp pat)   = "match" ++ " " ++ show_exp spc exp ++ " with " ++ show_exp spc pat
show_exp spc (EExp   _ exp)       = show_exp spc exp
show_exp spc e                    = error $ show e

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Stmt -> Stmt
map_stmt f@(fs,_,ft) (Class z id ctr ifc p)     = fs (Class z id ctr ifc' (map_stmt f p))
                                                    where ifc' = map (\(x,y,tp,z)->(x,y,ft tp,z)) ifc
map_stmt f@(fs,_,ft) (Inst  z cls tp imp p)     = fs (Inst  z cls tp imp' (map_stmt f p))
                                                    where imp' = map (\(x,y,tp,z)->(x,y,ft tp,z)) imp
map_stmt f@(fs,_,ft) (Data  z tp abs p)         = fs (Data  z (ft tp) abs (map_stmt f p))
map_stmt f@(fs,_,ft) (Var   z id tp p)          = fs (Var   z id (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (Match z b exp cses)       = fs (Match z b (map_exp f exp) (map (\(ds,pt,st) -> (map_stmt f ds, map_exp f pt, map_stmt f st)) cses))
map_stmt f@(fs,_,_)  (CallS z exp)              = fs (CallS z (map_exp f exp))
map_stmt f@(fs,_,_)  (Seq   z p1 p2)            = fs (Seq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Loop  z p)                = fs (Loop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (Ret   z exp)              = fs (Ret   z (map_exp f exp))
map_stmt f@(fs,_,_)  (Nop   z)                  = fs (Nop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Exp -> Exp
map_exp f@(_,fe,_)  (ECons  z id)    = fe (ECons  z id)
map_exp f@(_,fe,_)  (ETuple z es)    = fe (ETuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (EFunc  z tp p)  = fe (EFunc  z (ft tp) (map_stmt f p))
map_exp f@(_,fe,_)  (ECall  z e1 e2) = fe (ECall  z (map_exp f e1) (map_exp f e2))
map_exp f@(_,fe,_)  exp             = fe exp

--  class Equalable a where
--      eq :: a -> a -> Bool
--
--  instance Equalable X where
--      eq :: X -> X -> Bool
--      eq a b = ...
--
--  instance Equalable Int where
--      eq :: Int -> Int -> Bool
--      eq a b = <primitive>
--
--  eq 10 20    :: eq Int Int
--
-- To resolve call to `eq`:
--  * find associated `func`:
--      * top-level funcs
--      * class declarations
--      ! only one is allowed in the whole program
--      * in either case, check if type matches
--  * if found class:
--      * instantiate class variable `a` against call `eq 10 20`, resolving to `Int`
--          ! must find `instance Equable Int`
--
-- Expected layout of Inst.imp:
--  (Var _ "f" tp
--    (Seq _
--      (Write _ (LVar "f") (EFunc ...))   -- or (Nop _) // no implementation
--      (Var _ "g" tp                     -- or (Nop _) // eof
--        ...

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class z _ _ _ _)   = z
    getAnn (Inst  z _ _ _ _)   = z
    getAnn (Data  z _ _ _)     = z
    getAnn (Var   z _ _ _)     = z
    getAnn (Match z _ _ _)     = z
    getAnn (CallS z _)         = z
    getAnn (Seq   z _ _)       = z
    getAnn (Loop  z _)         = z
    getAnn (Ret   z _)         = z
    getAnn (Nop   z)           = z

prelude z p = (Data z (TData ["Int"]          [] TUnit,cz) False
              (Data z (TData ["Bool"]         [] TUnit,cz) True
              (Data z (TData ["Bool","True"]  [] TUnit,cz) False
              (Data z (TData ["Bool","False"] [] TUnit,cz) False p))))
