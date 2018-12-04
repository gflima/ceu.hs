module Ceu.Grammar.Check.VarEvt where

import Data.Char (toUpper)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: Stmt -> Errors
check p = aux [] [] p

aux vars ints s = case getStmt' s of

  Var var p     -> es++es' where
                   es' = aux (s:vars) ints p
                   es = if (take 2 var == "__") || (not $ contains var vars) then
                          []
                        else
                          [err_stmt_msg s "variable '" ++ var ++ "' is already declared"]

  Int int p     -> es++es' where
                   es' = aux vars (s:ints) p
                   es = if not $ contains int ints then [] else
                          [err_stmt_msg s "event '" ++ int ++ "' is already declared"]

  Write var exp -> es1++es2 where
                   es1 = if (map toUpper var)==var || contains var vars then [] else
                          [err_stmt_msg s "variable '" ++ var ++ "' is not declared"]
                   es2 = getErrs vars exp

  AwaitInt int  -> if contains int ints then [] else
                    [err_stmt_msg s "event '" ++ int ++ "' is not declared"]

  EmitInt int   -> if contains int ints then [] else
                    [err_stmt_msg s "event '" ++ int ++ "' is not declared"]

  If exp p1 p2  -> es ++ (aux vars ints p1) ++ (aux vars ints p2) where
                   es = getErrs vars exp

  Seq p1 p2     -> (aux vars ints p1) ++ (aux vars ints p2)
  Loop p        -> (aux vars ints p)
  Every evt p   -> es ++ (aux vars ints p) where
                   es = if (map toUpper evt)==evt || contains evt ints then [] else
                          [err_stmt_msg s "event '" ++ evt ++ "' is not declared"]
            
  Par p1 p2     -> (aux vars ints p1) ++ (aux vars ints p2)
  Pause var p   -> es ++ (aux vars ints p) where
                   es = if contains var vars then [] else
                          [err_stmt_msg s "variable '" ++ var ++ "' is not declared"]
  Fin p         -> (aux vars ints p)
  Trap p        -> (aux vars ints p)
  otherwise     -> []

-------------------------------------------------------------------------------

contains :: String -> [Stmt] -> Bool
contains id dcls = elem id $ map f dcls where
                    f dcl = case getStmt' dcl of
                              Var var _ -> var
                              Int int _ -> int

-------------------------------------------------------------------------------

getErrs :: [Stmt] -> Exp -> Errors
getErrs vars exp = case getExp' exp of
  Read var  -> if (map toUpper var)==var || contains var vars then [] else
                              [err_exp_msg exp "variable '" ++ var ++ "' is not declared"]
  Umn e     -> getErrs vars e
  Add e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  Sub e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  Mul e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  Div e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  Equ e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  Lte e1 e2 -> (getErrs vars e1) ++ (getErrs vars e2)
  otherwise -> []
