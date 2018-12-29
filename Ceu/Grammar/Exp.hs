module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals  (Val, ID_Func, ID_Var)
import Ceu.Grammar.Ann      (Ann)

data RawAt ann = RawAtE (Exp ann) | RawAtS String
  deriving (Eq, Show)

data Exp ann
    = RawE   ann [RawAt ann]        -- {@(ceu)+c}
    | Const  ann Val                -- 1
    | Read   ann ID_Var             -- a ; xs
    | Unit   ann                    -- ()
    -- | Parens ann (Exp ann)          -- (1) ; (f 1) ; (f (1,2)) ; (())
    | Tuple  ann [Exp ann]          -- (1,2) ; ((1),2) ; ((1,2),3) ; ((),()) // (len >= 2)
    | Call   ann ID_Func (Exp ann)  -- f a ; f(a) ; f(1,2)
    deriving (Eq, Show)

getAnn :: (Ann a) => Exp a -> a
getAnn (RawE  z _)   = z
getAnn (Const z _)   = z
getAnn (Read  z _)   = z
getAnn (Unit  z)     = z
getAnn (Tuple z _)   = z
getAnn (Call  z _ _) = z

{-
exp2word :: Exp ann -> String
exp2word (RawE   _ _)  = "raw"
exp2word (Const  _ _)  = "constant"
exp2word (Unit   _)    = "unit"
exp2word (Tuple  _ _)  = "tuple"
exp2word (Read  _ _)   = "read"
exp2word (Call  _ _ _) = "call"
-}
