module Ceu.Grammar.Basic where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type     (Type(..))

-------------------------------------------------------------------------------

data Exp
    = Number Ann Int            -- 1
    | Cons   Ann ID_Type        -- True
    | Read   Ann ID_Var         -- a ; xs
    | Unit   Ann                -- ()
    | Tuple  Ann [Exp]          -- (1,2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Call   Ann ID_Func Exp    -- f a ; f(a) ; f(1,2)
    | SCall  Ann ID_Func Exp    -- f__int a
    deriving (Eq, Show)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (Number z _)   = z
    getAnn (Cons   z _)   = z
    getAnn (Read   z _)   = z
    getAnn (Unit   z)     = z
    getAnn (Tuple  z _)   = z
    getAnn (Call   z _ _) = z
    getAnn (SCall  z _ _) = z

-------------------------------------------------------------------------------

data Stmt
    = Class  Ann ID_Class [ID_Var] Stmt Stmt  -- new class declaration
    | Inst   Ann ID_Class [Type] Stmt Stmt    -- new class instance
    | Data   Ann ID_Type [ID_Var] [DataCons] Bool Stmt -- new type declaration
    | Var    Ann ID_Var  Type Stmt            -- variable declaration
    | Func   Ann ID_Func Type Stmt            -- function declaration
    | FuncI  Ann ID_Func Type Stmt Stmt       -- function implementation (must have accompainying Func)
    | Write  Ann Loc Exp                      -- assignment statement
    | CallS  Ann ID_Func Exp                  -- call function
    | SCallS Ann ID_Func Exp                  -- resolved call function
    | If     Ann Exp Stmt Stmt                -- conditional
    | Seq    Ann Stmt Stmt                    -- sequence
    | Loop   Ann Stmt                         -- infinite loop
    | Ret    Ann Exp                          -- terminate program with Ret
    | Nop    Ann                              -- dummy statement (internal)
    deriving (Eq, Show)

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

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class  z _ _ _ _)   = z
    getAnn (Inst   z _ _ _ _)   = z
    getAnn (Data   z _ _ _ _ _) = z
    getAnn (Var    z _ _ _)     = z
    getAnn (Func   z _ _ _)     = z
    getAnn (FuncI  z _ _ _ _)   = z
    getAnn (Write  z _ _)       = z
    getAnn (CallS  z _ _)       = z
    getAnn (SCallS z _ _)       = z
    getAnn (If     z _ _ _)     = z
    getAnn (Seq    z _ _)       = z
    getAnn (Loop   z _)         = z
    getAnn (Ret    z _)         = z
    getAnn (Nop    z)           = z

prelude z p = (Data z "Int" [] [] False p)
