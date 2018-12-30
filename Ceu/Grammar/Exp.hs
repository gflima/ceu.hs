module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals  (Val, ID_Func, ID_Var)
import Ceu.Grammar.Ann      (Ann)

data RawAt = RawAtE Exp | RawAtS String
  deriving (Eq, Show)

data Exp
    = RawE   Ann [RawAt]        -- {@(ceu)+c}
    | Const  Ann Val            -- 1
    | Read   Ann ID_Var         -- a ; xs
    | Unit   Ann                -- ()
    -- | Parens Ann Exp         -- (1) ; (f 1) ; (f (1,2)) ; (())
    | Tuple  Ann [Exp]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Call   Ann ID_Func Exp    -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

getAnnE :: Exp -> Ann
getAnnE (RawE  z _)   = z
getAnnE (Const z _)   = z
getAnnE (Read  z _)   = z
getAnnE (Unit  z)     = z
getAnnE (Tuple z _)   = z
getAnnE (Call  z _ _) = z

{-
exp2word :: Exp ann -> String
exp2word (RawE   _ _)  = "raw"
exp2word (Const  _ _)  = "constant"
exp2word (Unit   _)    = "unit"
exp2word (Tuple  _ _)  = "tuple"
exp2word (Read  _ _)   = "read"
exp2word (Call  _ _ _) = "call"
-}
