module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals

-- Expession.
data Exp ann
  = Const ann Val                 -- constant
  | Read  ann ID_Var              -- variable read
  | Umn   ann (Exp ann)           -- unary minus
  | Add   ann (Exp ann) (Exp ann) -- addition
  | Sub   ann (Exp ann) (Exp ann) -- subtraction
  | Mul   ann (Exp ann) (Exp ann) -- multiplication
  | Div   ann (Exp ann) (Exp ann) -- division
  | Equ   ann (Exp ann) (Exp ann) -- `==` equal
  | Lte   ann (Exp ann) (Exp ann) -- `<=` less-than-equal
  deriving (Eq, Show)

eEqu a b = Equ () a b
eLte a b = Lte () a b
eAdd a b = Add () a b
eSub a b = Sub () a b
eMul a b = Mul () a b
eDiv a b = Div () a b

infixl 5 `eEqu` -- `Equ` associates to the left
infixl 5 `eLte` -- `Lte` associates to the left
infixl 6 `eAdd` -- `Add` associates to the left
infixl 6 `eSub` -- `Sub` associates to the left
infixl 7 `eMul` -- `Mul` associates to the left
infixl 7 `eDiv` -- `Div` associates to the left

getAnn :: Exp ann -> ann
getAnn (Const z _)   = z
getAnn (Read  z _)   = z
getAnn (Umn   z _)   = z
getAnn (Add   z _ _) = z
getAnn (Sub   z _ _) = z
getAnn (Mul   z _ _) = z
getAnn (Div   z _ _) = z
getAnn (Equ   z _ _) = z
getAnn (Lte   z _ _) = z

-- Shows expression.
showExp :: Exp ann -> String
showExp expr = case expr of
  Const _ n     -> show n
  Read  _ v     -> v
  Umn   _ e     -> printf "(-%s)"    (showExp e)
  Add   _ e1 e2 -> printf "(%s+%s)"  (showExp e1) (showExp e2)
  Sub   _ e1 e2 -> printf "(%s-%s)"  (showExp e1) (showExp e2)
  Mul   _ e1 e2 -> printf "(%s*%s)"  (showExp e1) (showExp e2)
  Div   _ e1 e2 -> printf "(%s/%s)"  (showExp e1) (showExp e2)
  Equ   _ e1 e2 -> printf "(%s==%s)" (showExp e1) (showExp e2)
  Lte   _ e1 e2 -> printf "(%s<=%s)" (showExp e1) (showExp e2)

-------------------------------------------------------------------------------

exp2word :: Exp ann -> String
exp2word ext = case ext of
  Const _ n   -> "constant " ++ (show n)
  Read  _ var -> "read access to '" ++ var ++ "'"
  Umn   _ _   -> "unary minus"
  Add   _ _ _ -> "addition"
  Sub   _ _ _ -> "subtraction"
  Mul   _ _ _ -> "multiplication"
  Div   _ _ _ -> "division"
  Equ   _ _ _ -> "equal comparison"
  Lte   _ _ _ -> "less-then comparison"

instance (ToSourceString ann) => INode (Exp ann) where
  toWord       = exp2word
  toSource exp = toSourceString $ getAnn exp
