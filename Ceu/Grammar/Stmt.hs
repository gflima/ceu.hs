module Ceu.Grammar.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, HasAnn(..), annz)
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp      (Exp(..), RawAt)
import Text.Printf

-- Program (pg 5).
data Stmt
  = Class Ann ID_Class [ID_Var] Stmt Stmt  -- new class declaration
  | Inst  Ann ID_Class [ID_Type] Stmt Stmt -- new class instance
  | Data  Ann ID_Type [ID_Var] [DataCons] Bool Stmt -- new type declaration
  | Var   Ann ID_Var  Type Stmt            -- variable declaration
  | Func  Ann ID_Func Type Stmt            -- function declaration
  | FuncI Ann ID_Func Type Stmt Stmt       -- function implementation (must have accompainying Func)
  | Write Ann Loc Exp                      -- assignment statement
  | CallS Ann ID_Func Exp                  -- call function
  | If    Ann Exp Stmt Stmt                -- conditional
  | Seq   Ann Stmt Stmt                    -- sequence
  | Loop  Ann Stmt                         -- infinite loop
  | Nop   Ann                              -- dummy statement (internal)
  deriving (Eq, Show)

sSeq a b = Seq annz a b
infixr 1 `sSeq`

instance HasAnn Stmt where
    --getAnn :: Stmt -> Ann
    getAnn (Class z _ _ _ _)   = z
    getAnn (Inst  z _ _ _ _)   = z
    getAnn (Data  z _ _ _ _ _) = z
    getAnn (Var   z _ _ _)     = z
    getAnn (Func  z _ _ _)     = z
    getAnn (FuncI z _ _ _ _)   = z
    getAnn (Write z _ _)       = z
    getAnn (CallS z _ _)       = z
    getAnn (If    z _ _ _)     = z
    getAnn (Seq   z _ _)       = z
    getAnn (Loop  z _)         = z
    getAnn (Nop   z)           = z
