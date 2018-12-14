module Ceu.Grammar.Id where

import Data.Char (toUpper)
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (Ann ann) => (Stmt ann) -> Errors
check p = stmt [] p

stmt :: (Ann ann) => [Stmt ann] -> Stmt ann -> Errors

stmt ids s@(Var _ id p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Inp _ id p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Out _ id p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Evt _ id p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)

stmt ids s@(Write    _ id exp) = (errUndeclaredInvalid ids (id,s) isVar) ++ (expr ids exp)
stmt ids s@(AwaitInp _ id)     = (errUndeclaredInvalid ids (id,s) isInp)
stmt ids s@(EmitExt  _ id exp) = (errUndeclaredInvalid ids (id,s) isExt) ++ es
                                 where
                                    es = case exp of
                                        Nothing -> []
                                        Just e  -> (expr ids e)
stmt ids s@(AwaitEvt _ id)     = (errUndeclaredInvalid ids (id,s) isEvt)
stmt ids s@(EmitEvt  _ id)     = (errUndeclaredInvalid ids (id,s) isEvt)

stmt ids (If  _ exp p1 p2) = (expr ids exp) ++ (stmt ids p1) ++ (stmt ids p2)
stmt ids (Seq _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Loop _ p)        = (stmt ids p)
stmt ids s@(Every _ evt p) = (errUndeclaredInvalid ids (evt,s) isInpEvt) ++ (stmt ids p)
stmt ids (Par _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids s@(Pause _ id p) = (errUndeclaredInvalid ids (id,s) isVar) ++ (stmt ids p)
stmt ids (Fin _ p)         = (stmt ids p)
stmt ids (Trap _ p)        = (stmt ids p)
stmt ids p                 = []

-------------------------------------------------------------------------------

isVar (Var _ _ _) = True
isVar _           = False

isExt (Inp _ _ _) = True
isExt (Out _ _ _) = True
isExt _           = False

isInp (Inp _ _ _) = True
isInp _           = False

isEvt (Evt _ _ _) = True
isEvt _           = False

isInpEvt (Inp _ _ _) = True
isInpEvt (Evt _ _ _) = True
isInpEvt _           = False

getId :: Stmt ann -> String
getId (Var      _ id _) = id
getId (Inp      _ id _) = id
getId (Out      _ id _) = id
getId (Evt      _ id _) = id

find' :: String -> [Stmt ann] -> Maybe (Stmt ann)
find' id ids = find (\s -> getId s == id) ids

errDeclared :: (INode a) => [Stmt ann] -> (String,a) -> Errors
errDeclared ids (id,dcl) =
    if (take 2 id == "__") then [] else    -- nested par/and (__and)
        case find' id ids of
            Nothing   -> []
            s         -> [toError dcl "identifier '" ++ id ++ "' is already declared"]

errUndeclaredInvalid :: (INode a) => [Stmt ann] -> (String,a) -> (Stmt ann -> Bool) -> Errors
errUndeclaredInvalid ids (id,use) pred =
    case find' id ids of
        Nothing  -> [toError use "identifier '" ++ id ++ "' is not declared"]
        (Just s) -> if pred s then [] else
                        [toError use "identifier '" ++ id ++ "' is invalid"]

-------------------------------------------------------------------------------

expr :: (Ann ann) => [Stmt ann] -> Exp ann -> Errors
expr ids e@(Read _ id) = if (map toUpper id) == id then [] else -- payload of input events (eg, _X)
                            errUndeclaredInvalid ids (id,e) isVar
expr ids (Umn _ e)      = expr ids e
expr ids (Add _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Sub _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Mul _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Div _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Equ _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids (Lte _ e1 e2)  = (expr ids e1) ++ (expr ids e2)
expr ids _              = []
