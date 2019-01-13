module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals  (ID_Type, ID_Func, ID_Var)
import Ceu.Grammar.Ann      (Ann,HasAnn(..))

data RawAt = RawAtE Exp | RawAtS String
  deriving (Eq, Show)

data Exp
    = Number Ann Int            -- 1
    | Cons   Ann ID_Type        -- True
    | Read   Ann ID_Var         -- a ; xs
    | Unit   Ann                -- ()
    | Tuple  Ann [Exp]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Call   Ann ID_Func Exp    -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

instance HasAnn Exp where
    --getAnn :: Exp -> Ann
    getAnn (Number z _)   = z
    getAnn (Cons   z _)   = z
    getAnn (Read   z _)   = z
    getAnn (Unit   z)     = z
    getAnn (Tuple  z _)   = z
    getAnn (Call   z _ _) = z
