module Ceu.Grammar.Basic where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type     (Type(..))
import Data.List            (intercalate)

-------------------------------------------------------------------------------

data Exp
    = Error  Ann Int
    | Unit   Ann                -- ()
    | Number Ann Int            -- 1
    | Cons   Ann ID_Data_Hier Exp  -- Bool.True ; Tree.Node (Tree.Leaf,1,Tree.Leaf)
    | Read   Ann ID_Var         -- a ; xs
    | Arg    Ann
    | Tuple  Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Func   Ann Type Stmt      -- function implementation
    | Call   Ann Exp Exp        -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

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

-------------------------------------------------------------------------------

data Stmt
    = Class  Ann (ID_Class,[ID_Var]) [(ID_Class,[ID_Var])] [(Ann,ID_Var,Type,Bool)] Stmt -- new class declaration
    | Inst   Ann (ID_Class,[Type])                         [(Ann,ID_Var,Type,Bool)] Stmt -- new class instance
    | Data   Ann ID_Data_Hier [ID_Var] Type Bool Stmt -- new type declaration
    | Var    Ann ID_Var Bool Type Stmt        -- variable declaration
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
show_stmt spc (Data _ id _ _ _ p)     = replicate spc ' ' ++ "data "   ++ intercalate "." id ++ "\n" ++ show_stmt spc p
show_stmt spc (Var _ id _ _ p)        = replicate spc ' ' ++ "var "    ++ id ++ "\n" ++ show_stmt spc p
show_stmt spc (CallS _ e)             = replicate spc ' ' ++ "call " ++ show_exp spc e
show_stmt spc (Ret _ e)               = replicate spc ' ' ++ "return " ++ show_exp spc e
show_stmt spc (Seq _ p1 p2)           = replicate spc ' ' ++ "--\n" ++ show_stmt (spc+4) p1 ++
                                        replicate spc ' ' ++ "--\n" ++ show_stmt (spc+4) p2
show_stmt spc (Match _ _ loc e p1 p2) = replicate spc ' ' ++ show_loc loc ++ " = " ++ show_exp spc e ++ "\n" ++ show_stmt spc p1
show_stmt spc (Nop _)                 = replicate spc ' ' ++ "nop"
show_stmt spc p = error $ show p

show_exp :: Int -> Exp -> String
show_exp spc (Number _ n)   = show n
show_exp spc (Cons _ _ _)   = "cons"
show_exp spc (Read _ id)    = id
show_exp spc (Arg _)        = "arg"
show_exp spc (Tuple _ es)   = "(" ++ intercalate "," (map (show_exp spc) es) ++ ")"
show_exp spc (Func _ _ p)   = "func" ++ "\n" ++ show_stmt (spc+4) p
show_exp spc (Call _ e1 e2) = "call" ++ " " ++ show_exp spc e1 ++ " " ++ show_exp spc e2
show_exp spc e              = show e

show_loc :: Loc -> String
show_loc (LVar id)   = id
show_loc (LTuple ls) = "(" ++ intercalate "," (map show_loc ls) ++ ")"
show_loc l = show l

-------------------------------------------------------------------------------

map_stmt :: (Stmt->Stmt, Exp->Exp, Type->Type) -> Stmt -> Stmt
map_stmt f@(fs,_,ft) (Class z me ext ifc p)     = fs (Class z me ext ifc' (map_stmt f p))
                                                    where ifc' = map (\(x,y,tp,z)->(x,y,ft tp,z)) ifc
map_stmt f@(fs,_,ft) (Inst  z me imp p)         = fs (Inst  z me imp' (map_stmt f p))
                                                    where imp' = map (\(x,y,tp,z)->(x,y,ft tp,z)) imp
map_stmt f@(fs,_,ft) (Data  z me flds tp abs p) = fs (Data  z me flds (ft tp) abs (map_stmt f p))
map_stmt f@(fs,_,ft) (Var   z id gen tp p)      = fs (Var   z id gen (ft tp) (map_stmt f p))
map_stmt f@(fs,_,_)  (Match z b loc exp p1 p2)  = fs (Match z b loc (map_exp f exp) (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (CallS z exp)              = fs (CallS z (map_exp f exp))
map_stmt f@(fs,_,_)  (Seq   z p1 p2)            = fs (Seq   z (map_stmt f p1) (map_stmt f p2))
map_stmt f@(fs,_,_)  (Loop  z p)                = fs (Loop  z (map_stmt f p))
map_stmt f@(fs,_,_)  (Ret   z exp)              = fs (Ret   z (map_exp f exp))
map_stmt f@(fs,_,_)  (Nop   z)                  = fs (Nop   z)

map_exp :: (Stmt->Stmt, Exp->Exp, Type->Type) -> Exp -> Exp
map_exp f@(_,fe,_)  (Cons  z id e)  = fe (Cons  z id (map_exp f e))
map_exp f@(_,fe,_)  (Tuple z es)    = fe (Tuple z (map (map_exp f) es))
map_exp f@(_,fe,ft) (Func  z tp p)  = fe (Func  z (ft tp) (map_stmt f p))
map_exp f@(_,fe,_)  (Call  z e1 e2) = fe (Call  z (map_exp f e1) (map_exp f e2))
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
--      (Write _ (LVar "f") (Func ...))   -- or (Nop _) // no implementation
--      (Var _ "g" tp                     -- or (Nop _) // eof
--        ...

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class z _ _ _ _)   = z
    getAnn (Inst  z _ _ _)     = z
    getAnn (Data  z _ _ _ _ _) = z
    getAnn (Var   z _ _ _ _)   = z
    getAnn (Match z _ _ _ _ _) = z
    getAnn (CallS z _)         = z
    getAnn (Seq   z _ _)       = z
    getAnn (Loop  z _)         = z
    getAnn (Ret   z _)         = z
    getAnn (Nop   z)           = z

prelude z p = (Data z ["Int"]        [] Type0 False
              (Data z ["Bool"]       [] Type0 False
              (Data z ["Bool.True"]  [] Type0 False
              (Data z ["Bool.False"] [] Type0 False p))))
