module Ceu.Grammar.Check.VarEvt where

import Data.Char (toUpper)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: Stmt -> Errors
check p = aux [] [] p

aux vars ints s@(Var var p)   = es++es' where
                                 es' = aux (s:vars) ints p
                                 es = if (take 2 var == "__") || (not $ contains var vars) then
                                        []
                                      else
                                        [err_stmt_msg s "variable '" ++ var ++ "' is already declared"]

aux vars ints s@(Int int p)   = es++es' where
                                 es' = aux vars (s:ints) p
                                 es = if not $ contains int ints then [] else
                                       [err_stmt_msg s "event '" ++ int ++ "' is already declared"]

aux vars _ s@(Write var exp)  = es1++es2 where
                                 es1 = if (map toUpper var)==var || contains var vars then [] else
                                         [err_stmt_msg s "variable '" ++ var ++ "' is not declared"]
                                 es2 = getErrs vars exp

aux _ ints s@(AwaitInt int)   = if contains int ints then [] else
                                  [err_stmt_msg s "event '" ++ int ++ "' is not declared"]

aux _ ints s@(EmitInt int)    = if contains int ints then [] else
                                  [err_stmt_msg s "event '" ++ int ++ "' is not declared"]

aux vars ints (If exp p1 p2)  = es ++ (aux vars ints p1) ++ (aux vars ints p2) where
                                 es = getErrs vars exp

aux vars ints (Seq p1 p2)     = (aux vars ints p1) ++ (aux vars ints p2)
aux vars ints (Loop p)        = (aux vars ints p)
aux vars ints s@(Every evt p) = es ++ (aux vars ints p) where
                                es = if (map toUpper evt)==evt || contains evt ints then [] else
                                      [err_stmt_msg s "event '" ++ evt ++ "' is not declared"]
            
aux vars ints (Par p1 p2)     = (aux vars ints p1) ++ (aux vars ints p2)
aux vars ints s@(Pause var p) = es ++ (aux vars ints p) where
                                 es = if contains var vars then [] else
                                      [err_stmt_msg s "variable '" ++ var ++ "' is not declared"]
aux vars ints (Fin p)         = (aux vars ints p)
aux vars ints (Trap p)        = (aux vars ints p)
aux vars ints p               = []

-------------------------------------------------------------------------------

contains :: String -> [Stmt] -> Bool
contains id dcls = elem id $ map f dcls where
                    f (Var var _) = var
                    f (Int int _) = int

-------------------------------------------------------------------------------

getErrs :: [Stmt] -> Exp -> Errors
getErrs vars e@(Read var) = if (map toUpper var)==var || contains var vars then [] else
                              [err_exp_msg e "variable '" ++ var ++ "' is not declared"]
getErrs vars (Umn e)      = getErrs vars e
getErrs vars (Add e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Sub e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Mul e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Div e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Equ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Lte e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars _            = []
