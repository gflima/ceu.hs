module Ceu.Globals where

import Text.Printf

-- Primitive types.
type ID_Var  = String           -- variable identifier
type ID_Evt  = String           -- event identifier
type Val = Int                  -- value

-- Special events:
-- "BOOT"
-- "FOREVER"

-- Expression.
data Expr
  = Const Val                   -- constant
  | Read ID_Var                 -- variable read
  | Umn Expr                    -- unary minus
  | Add Expr Expr               -- addition
  | Sub Expr Expr               -- subtraction
  | Mul Expr Expr               -- multiplication
  | Div Expr Expr               -- division
  deriving (Eq, Show)

infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left
infixl 7 `Mul`                  -- `Mul` associates to the left
infixl 7 `Div`                  -- `Div` associates to the left

-- Shows expression.
showExpr :: Expr -> String
showExpr expr = case expr of
  Const n   -> show n
  Read v    -> v
  Umn e     -> printf "(-%s)" (showExpr e)
  Add e1 e2 -> printf "(%s+%s)" (showExpr e1) (showExpr e2)
  Sub e1 e2 -> printf "(%s-%s)" (showExpr e1) (showExpr e2)
  Mul e1 e2 -> printf "(%s*%s)" (showExpr e1) (showExpr e2)
  Div e1 e2 -> printf "(%s*%s)" (showExpr e1) (showExpr e2)
