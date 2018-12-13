module Ceu.Grammar.VarEvt where

import Data.Char (toUpper)
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (Ann ann) => (Stmt ann) -> Errors
check p = stmt [] p

stmt :: (Ann ann) => [Stmt ann] -> Stmt ann -> Errors

stmt ids s@(Var _ var p)   = (errDeclared ids (var,s)) ++ (stmt (s:ids) p)
stmt ids s@(Int _ int p)   = (errDeclared ids (int,s)) ++ (stmt (s:ids) p)
stmt ids s@(Out _ ext p)   = (errDeclared ids (ext,s)) ++ (stmt (s:ids) p)

stmt ids s@(Write    _ var exp) = (errUndeclaredInvalid ids (var,s) isVar) ++ (expr ids exp)
stmt ids s@(AwaitInt _ int)     = (errUndeclaredInvalid ids (int,s) isInt)
stmt ids s@(EmitInt  _ int)     = (errUndeclaredInvalid ids (int,s) isInt)

stmt ids (If  _ exp p1 p2) = (expr ids exp) ++ (stmt ids p1) ++ (stmt ids p2)
stmt ids (Seq _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Loop _ p)        = (stmt ids p)
stmt ids s@(Every _ evt p) = (errUndeclaredInvalid ids (evt,s) isEvt) ++ (stmt ids p)
stmt ids (Par _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids s@(Pause _ var p) = (errUndeclaredInvalid ids (var,s) isVar) ++ (stmt ids p)
stmt ids (Fin _ p)         = (stmt ids p)
stmt ids (Trap _ p)        = (stmt ids p)
stmt ids p                 = []

-------------------------------------------------------------------------------

isVar (Var _ _ _) = True
isVar _           = False

isInt (Int _ _ _) = True
isInt _           = False

isEvt (Int _ _ _) = True
isEvt _           = False

getId :: Stmt ann -> String
getId (Var      _ var _) = var
getId (Int      _ int _) = int
getId (Out      _ ext _) = ext

find' :: String -> [Stmt ann] -> Maybe (Stmt ann)
find' id ids = find (\s -> getId s == id) ids

errDeclared :: (INode a) => [Stmt ann] -> (String,a) -> Errors
errDeclared ids (id,dcl) =
    case find' id ids of
        Nothing   -> []
        s         -> [toError dcl "identifier '" ++ id ++ "' is already declared"]

errUndeclaredInvalid :: (INode a) => [Stmt ann] -> (String,a) -> (Stmt ann -> Bool) -> Errors
errUndeclaredInvalid ids (id,use) pred =
    case find' id ids of
        Nothing  -> [toError use "identifier '" ++ id ++ "' is not declared"]
        (Just s) -> if pred s then [] else
                        [toError use "identifier '" ++ id ++ "' is invalid"]

    -- if (take 2 var == "__") || (not $ contains var ids) then

-------------------------------------------------------------------------------

expr :: (Ann ann) => [Stmt ann] -> Exp ann -> Errors
expr ids e@(Read _ var) = errUndeclaredInvalid ids (var,e) isVar
expr ids (Umn _ e)      = expr ids e
expr ids (Add _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Sub _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Mul _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Div _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Equ _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Lte _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids _              = []
