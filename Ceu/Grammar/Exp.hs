module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals

-- Expession.
data Exp
  = Const Val                   -- constant
  | Read ID_Var                 -- variable read
  | Umn Exp                     -- unary minus
  | Add Exp Exp                 -- addition
  | Sub Exp Exp                 -- subtraction
  | Mul Exp Exp                 -- multiplication
  | Div Exp Exp                 -- division
  | Equ Exp Exp                 -- `==` equal
  | Lte Exp Exp                 -- `<=` less-than-equal
  deriving (Eq, Show)

infixl 5 `Equ`                  -- `Equ` associates to the left
infixl 5 `Lte`                  -- `Lte` associates to the left
infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left
infixl 7 `Mul`                  -- `Mul` associates to the left
infixl 7 `Div`                  -- `Div` associates to the left

-- Shows expression.
showExp :: Exp -> String
showExp expr = case expr of
  Const n   -> show n
  Read v    -> v
  Umn e     -> printf "(-%s)"    (showExp e)
  Add e1 e2 -> printf "(%s+%s)"  (showExp e1) (showExp e2)
  Sub e1 e2 -> printf "(%s-%s)"  (showExp e1) (showExp e2)
  Mul e1 e2 -> printf "(%s*%s)"  (showExp e1) (showExp e2)
  Div e1 e2 -> printf "(%s/%s)"  (showExp e1) (showExp e2)
  Equ e1 e2 -> printf "(%s==%s)" (showExp e1) (showExp e2)
  Lte e1 e2 -> printf "(%s<=%s)" (showExp e1) (showExp e2)

-------------------------------------------------------------------------------

exp2word :: Exp -> String
exp2word ext = case ext of
  Const n       -> "constant " ++ (show n)
  Read var      -> "read access to '" ++ var ++ "'"
  Umn _         -> "unary minus"
  Add _ _       -> "addition"
  Sub _ _       -> "subtraction"
  Mul _ _       -> "multiplication"
  Div _ _       -> "division"
  Equ _ _       -> "equal comparison"
  Lte _ _       -> "less-then comparison"

err_exp_msg :: Exp -> String -> String
err_exp_msg exp msg = (exp2word exp) ++ ": " ++ msg
