module Ceu.Grammar.Basic where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann                (Ann, HasAnn(..), annz)
import Ceu.Grammar.Constraints as Cs  (Map, cz)
import Ceu.Grammar.Type        as T   (TypeC, Type(..), show', hier2str)
import Data.List                      (intercalate)

-------------------------------------------------------------------------------

data Exp
    = EError Ann Int
    | EVar   Ann ID_Var         -- a ; xs
    | EUnit  Ann                -- ()
    | EData  Ann ID_Data_Hier   -- Bool.True ; Int.1 ; Tree.Node
    | ETuple Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | EFunc  Ann TypeC Stmt     -- function implementation
    | ECall  Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    | EAny   Ann
    | EArg   Ann
    | EExp   Ann Exp
    deriving (Eq, Show)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (EError z _)   = z
    getAnn (EVar   z _)   = z
    getAnn (EUnit  z)     = z
    getAnn (EData  z _)   = z
    getAnn (ETuple z _)   = z
    getAnn (EFunc  z _ _) = z
    getAnn (ECall  z _ _) = z
    getAnn (EAny   z)     = z
    getAnn (EArg   z)     = z
    getAnn (EExp   z _)   = z

-------------------------------------------------------------------------------

data Loc = LAny
         | LVar ID_Var
         | LUnit
         | LCons ID_Data_Hier Loc
         | LTuple [Loc]
         | LExp Exp
  deriving (Eq, Show)

-------------------------------------------------------------------------------

data Stmt
    = Class  Ann ID_Class Cs.Map [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class declaration
    | Inst   Ann ID_Class TypeC  [(Ann,ID_Var,TypeC,Bool)] Stmt -- new class instance
    | Data   Ann TypeC Bool Stmt              -- new type declaration
    | Var    Ann ID_Var TypeC Stmt            -- variable declaration
    | Match  Ann Bool Loc Exp Stmt Stmt       -- match/assignment/if statement
    | CallS  Ann Exp                          -- call function
    | Seq    Ann Stmt Stmt                    -- sequence
    | Loop   Ann Stmt                         -- infinite loop
    | Ret    Ann Exp                          -- terminate program with Ret
    | Nop    Ann                              -- dummy statement (internal)
    deriving (Eq, Show)

-------------------------------------------------------------------------------

show_stmt :: Int -> Stmt -> String
--show_stmt spc (Class _ (id,_) _ _ p) = replicate spc ' ' ++ "class "  ++ id ++ "\n" ++ show_stmt spc p
--show_stmt spc (Inst  _ (id,_) _ p)   = replicate spc ' ' ++ "inst "   ++ id ++ "\n" ++ show_stmt spc p
show_stmt spc (Data _ (TData id _ _,_) _ p) = replicate spc ' ' ++ "data "   ++ intercalate "." id ++ "\n" ++ show_stmt spc p
show_stmt spc (Var _ id (tp,_) p)     = replicate spc ' ' ++ "var "    ++ id ++ ": " ++ T.show' tp ++ "\n" ++ show_stmt spc p
show_stmt spc (CallS _ e)             = replicate spc ' ' ++ "call " ++ show_exp spc e
show_stmt spc (Ret _ e)               = replicate spc ' ' ++ "return " ++ show_exp spc e
show_stmt spc (Seq _ p1 p2)           = replicate spc ' ' ++ "--\n" ++ show_stmt (spc+4) p1 ++
                                        replicate spc ' ' ++ "--\n" ++ show_stmt (spc+4) p2
show_stmt spc (Match _ _ loc e p1 p2) = replicate spc ' ' ++ show_loc loc ++ " = " ++ show_exp spc e ++ "\n" ++ show_stmt spc p1
show_stmt spc (Nop _)                 = replicate spc ' ' ++ "nop"
show_stmt spc p = error $ show p

show_exp :: Int -> Exp -> String
show_exp spc (EData _ ["Int",n]) = n
show_exp spc (EData _ id)    = hier2str id
show_exp spc (EVar _ id)    = id
show_exp spc (EArg _)        = "arg"
show_exp spc (ETuple _ es)   = "(" ++ intercalate "," (map (show_exp spc) es) ++ ")"
show_exp spc (EFunc _ _ p)   = "func" ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (ECall _ e1 e2) = "call" ++ " " ++ show_exp spc e1 ++ " " ++ show_exp spc e2
show_exp spc e              = show e

show_loc :: Loc -> String
show_loc (LVar   id)  = id
show_loc (LTuple ls)  = "(" ++ intercalate "," (map show_loc ls) ++ ")"
show_loc (LExp   exp) = show_exp 0 exp
show_loc l = show l

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Stmt -> Stmt
map_stmt f@(fs,_,ft) (Class z id ctr ifc p)     = fs (Class z id ctr ifc' (map_stmt f p))
                                                    where ifc' = map (\(x,y,tp,z)->(x,y,ft tp,z)) ifc
map_stmt f@(fs,_,ft) (Inst  z cls tp imp p)     = fs (Inst  z cls tp imp' (map_stmt f p))
                                                    where imp' = map (\(x,y,tp,z)->(x,y,ft tp,z)) imp
map_stmt f@(fs,_,ft) (Data  z tp abs p)         = fs (Data  z (ft tp) abs (map_stmt f p))
map_stmt f@(fs,_,ft) (Var   z id tp p)          = fs (Var   z id (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (Match z b loc exp p1 p2)  = fs (Match z b loc (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (CallS z exp)              = fs (CallS z (map_exp f exp))
map_stmt f@(fs,_,_)  (Seq   z p1 p2)            = fs (Seq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Loop  z p)                = fs (Loop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (Ret   z exp)              = fs (Ret   z (map_exp f exp))
map_stmt f@(fs,_,_)  (Nop   z)                  = fs (Nop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, TypeC->TypeC) -> Exp -> Exp
map_exp f@(_,fe,_)  (EData  z id)    = fe (EData  z id)
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
    getAnn (Match z _ _ _ _ _) = z
    getAnn (CallS z _)         = z
    getAnn (Seq   z _ _)       = z
    getAnn (Loop  z _)         = z
    getAnn (Ret   z _)         = z
    getAnn (Nop   z)           = z

prelude z p = (Data z (TData ["Int"]          [] TUnit,cz) False
              (Data z (TData ["Bool"]         [] TUnit,cz) False
              (Data z (TData ["Bool","True"]  [] TUnit,cz) False
              (Data z (TData ["Bool","False"] [] TUnit,cz) False p))))
