module Ceu.Grammar.VarEvt where

import Data.Char (toUpper)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (ToSourceString ann) => (Stmt ann) -> Errors
check p = aux [] [] p

aux vars ints s@(Var _ var p)   = es++es' where
                                  es' = aux (s:vars) ints p
                                  es = if (take 2 var == "__") || (not $ contains var vars) then
                                        []
                                      else
                                        [toError s "variable '" ++ var ++ "' is already declared"]

aux vars ints s@(Int _ int p)   = es++es' where
                                  es' = aux vars (s:ints) p
                                  es = if not $ contains int ints then [] else
                                       [toError s "event '" ++ int ++ "' is already declared"]

aux vars _ s@(Write _ var exp)  = es1++es2 where
                                  es1 = if (map toUpper var)==var || contains var vars then [] else
                                         [toError s "variable '" ++ var ++ "' is not declared"]
                                  es2 = getErrs vars exp

aux _ ints s@(AwaitInt _ int)   = if contains int ints then [] else
                                  [toError s "event '" ++ int ++ "' is not declared"]

aux _ ints s@(EmitInt _ int)    = if contains int ints then [] else
                                  [toError s "event '" ++ int ++ "' is not declared"]

aux vars ints (If _ exp p1 p2)  = es ++ (aux vars ints p1) ++ (aux vars ints p2) where
                                  es = getErrs vars exp

aux vars ints (Seq _ p1 p2)     = (aux vars ints p1) ++ (aux vars ints p2)
aux vars ints (Loop _ p)        = (aux vars ints p)
aux vars ints s@(Every _ evt p) = es ++ (aux vars ints p) where
                                  es = if (map toUpper evt)==evt || contains evt ints then [] else
                                      [toError s "event '" ++ evt ++ "' is not declared"]
            
aux vars ints (Par _ p1 p2)     = (aux vars ints p1) ++ (aux vars ints p2)
aux vars ints s@(Pause _ var p) = es ++ (aux vars ints p) where
                                  es = if contains var vars then [] else
                                      [toError s "variable '" ++ var ++ "' is not declared"]
aux vars ints (Fin _ p)         = (aux vars ints p)
aux vars ints (Trap _ p)        = (aux vars ints p)
aux vars ints p                 = []

-------------------------------------------------------------------------------

contains :: String -> [Stmt ann] -> Bool
contains id dcls = elem id $ map f dcls where
                    f (Var _ var _) = var
                    f (Int _ int _) = int

-------------------------------------------------------------------------------

getErrs :: (ToSourceString ann) => [Stmt ann] -> Exp ann -> Errors
getErrs vars e@(Read _ var) = if (map toUpper var)==var || contains var vars then [] else
                                [toError e "variable '" ++ var ++ "' is not declared"]
getErrs vars (Umn _ e)      = getErrs vars e
getErrs vars (Add _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Sub _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Mul _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Div _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Equ _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars (Lte _ e1 e2)  = (getErrs vars e1) ++ (getErrs vars e2)
getErrs vars _              = []
