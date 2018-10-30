module Ceu.Globals where

import Text.Printf

-- Primitive types.
type ID_Var = String            -- variable identifier
type ID_Evt = String            -- event identifier
type ID_Ext = String            -- external event identifier
type ID_Int = String            -- internal event identifier
type Val    = Int               -- value

-- Special events:
-- "BOOT"
-- "FOREVER"

-- Expession.
data Exp
  = Const Val                   -- constant
  | Read ID_Var                 -- variable read
  | Umn Exp                     -- unary minus
  | Add Exp Exp                 -- addition
  | Sub Exp Exp                 -- subtraction
  | Mul Exp Exp                 -- multiplication
  | Div Exp Exp                 -- division
  deriving (Eq, Show)

infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left
infixl 7 `Mul`                  -- `Mul` associates to the left
infixl 7 `Div`                  -- `Div` associates to the left

-- Shows expression.
showExp :: Exp -> String
showExp expr = case expr of
  Const n   -> show n
  Read v    -> v
  Umn e     -> printf "(-%s)"   (showExp e)
  Add e1 e2 -> printf "(%s+%s)" (showExp e1) (showExp e2)
  Sub e1 e2 -> printf "(%s-%s)" (showExp e1) (showExp e2)
  Mul e1 e2 -> printf "(%s*%s)" (showExp e1) (showExp e2)
  Div e1 e2 -> printf "(%s/%s)" (showExp e1) (showExp e2)

-- Shows list of variables.
showVars :: [ID_Var] -> String
showVars vars = case vars of
  []     -> ""
  v:[]   -> v
  v:vars -> v ++ "," ++ showVars vars
