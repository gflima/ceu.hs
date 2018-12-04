{-# LANGUAGE CPP #-}

module Ceu.Grammar.Exp where

import Text.Printf

import Ceu.Grammar.Globals

data Exp' a
  = Const Val               -- constant
  | Read ID_Var             -- variable read
  | Umn a                   -- unary minus
  | Add a a                 -- addition
  | Sub a a                 -- subtraction
  | Mul a a                 -- multiplication
  | Div a a                 -- division
  | Equ a a                 -- `==` equal
  | Lte a a                 -- `<=` less-than-equal
  deriving (Eq, Show)

infixl 5 `Equ`                  -- `Equ` associates to the left
infixl 5 `Lte`                  -- `Lte` associates to the left
infixl 6 `Add`                  -- `Add` associates to the left
infixl 6 `Sub`                  -- `Sub` associates to the left
infixl 7 `Mul`                  -- `Mul` associates to the left
infixl 7 `Div`                  -- `Div` associates to the left

-------------------------------------------------------------------------------

#ifndef SOURCE

newtype Exp = Exp (Exp' Exp)
  deriving (Eq, Show)

newExp :: Exp' Exp -> Exp
newExp exp = Exp exp

getExp' :: Exp -> Exp' Exp
getExp' (Exp e) = e

getSource :: Exp -> (Maybe Source)
getSource _ = Nothing

#else

newtype Exp = Exp (Exp' Exp, Source)
  deriving (Eq, Show)

newExp :: Exp' Exp -> Exp
newExp exp = Exp (exp, ("",0,0))

getExp' :: Exp -> Exp' Exp
getExp' (Exp (e,_)) = e

getSource :: Exp -> (Maybe Source)
getSource (Exp (_,s)) = Just s

#endif

-------------------------------------------------------------------------------

-- Shows expression

showExp :: Exp -> String
showExp expr = case getExp' expr of
  Const n   -> show n
  Read v    -> v
  Umn e     -> printf "(-%s)"    (showExp e)
  Add e1 e2 -> printf "(%s+%s)"  (showExp e1) (showExp e2)
  Sub e1 e2 -> printf "(%s-%s)"  (showExp e1) (showExp e2)
  Mul e1 e2 -> printf "(%s*%s)"  (showExp e1) (showExp e2)
  Div e1 e2 -> printf "(%s/%s)"  (showExp e1) (showExp e2)
  Equ e1 e2 -> printf "(%s==%s)" (showExp e1) (showExp e2)
  Lte e1 e2 -> printf "(%s<=%s)" (showExp e1) (showExp e2)

exp2word :: Exp -> String
exp2word ext = case getExp' ext of
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
err_exp_msg exp msg = source ++ (exp2word exp) ++ ": " ++ msg where
  source = case getSource exp of
    Just (_, ln, cl) -> "(line "++(show ln)++", column "++(show cl)++"): "
    Nothing          -> ""
