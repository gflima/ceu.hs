module Ceu.Grammar.Id where

import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (Ann ann) => (Stmt ann) -> Errors
check p = stmt [] p

stmt :: (Ann ann) => [Stmt ann] -> Stmt ann -> Errors

stmt ids s@(Var _ id _ p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Inp _ id p)   = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Out _ id p)   = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Evt _ id p)   = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)

stmt ids s@(Write    _ id exp) = (errUndeclaredInvalid dcl (id,s) isVar) ++ es1 ++ es2
                                 where
                                    dcl      = find' id ids
                                    (tp,es1) = expr ids exp
                                    es2 = case dcl of
                                        Just s' ->
                                            case tp of
                                                Just tp'  -> checkType (getType s') tp' s
                                                otherwise -> []
                                        otherwise -> []

stmt ids s@(AwaitInp _ id)     = (errUndeclaredInvalid (find' id ids) (id,s) isInp)
stmt ids s@(EmitExt  _ id exp) = (errUndeclaredInvalid (find' id ids) (id,s) isExt) ++ es
                                 where
                                    es = case exp of
                                        Nothing -> []
                                        Just e  -> es where (_,es) = expr ids e
stmt ids s@(AwaitEvt _ id)     = (errUndeclaredInvalid (find' id ids) (id,s) isEvt)
stmt ids s@(EmitEvt  _ id)     = (errUndeclaredInvalid (find' id ids) (id,s) isEvt)

stmt ids s@(If  _ exp p1 p2) = es1 ++ es2 ++ (stmt ids p1) ++ (stmt ids p2)
                               where
                                (tp,es1) = (expr ids exp)
                                es2 = case tp of
                                    Just tp'  -> checkType ["Int"] tp' s
                                    otherwise -> []
stmt ids (Seq _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Loop _ p)        = (stmt ids p)
stmt ids s@(Every _ evt p) = (errUndeclaredInvalid (find' evt ids) (evt,s) isInpEvt) ++ (stmt ids p)
stmt ids (Par _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids s@(Pause _ id p)  = (errUndeclaredInvalid (find' id ids) (id,s) isVar) ++ (stmt ids p)
stmt ids (Fin _ p)         = (stmt ids p)
stmt ids (Trap _ p)        = (stmt ids p)
stmt ids p                 = []

-------------------------------------------------------------------------------

getType :: Stmt ann -> Type
getType (Var _ _ tp _) = tp

checkType :: (INode a) => Type -> Type -> a -> Errors
checkType [] [] s = []
checkType [] l  s = [toError s "types do not match"]
checkType l  [] s = [toError s "types do not match"]
checkType (tp1:l1) (tp2:l2) s
    | tp1 == tp2 = checkType l1 l2 s
    | otherwise  = ["types do not match"]

-------------------------------------------------------------------------------

isVar (Var _ _ _ _) = True
isVar _             = False

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
getId (Var _ id _ _) = id
getId (Inp _ id _)   = id
getId (Out _ id _)   = id
getId (Evt _ id _)   = id

find' :: String -> [Stmt ann] -> Maybe (Stmt ann)
find' id ids = find (\s -> getId s == id) ids

errDeclared :: (INode a) => [Stmt ann] -> (String,a) -> Errors
errDeclared ids (id,dcl) =
    if (take 2 id == "__") then [] else    -- nested par/and (__and)
        case find' id ids of
            Nothing   -> []
            s         -> [toError dcl "identifier '" ++ id ++ "' is already declared"]

errUndeclaredInvalid :: (INode a) => Maybe (Stmt ann) -> (String,a) -> (Stmt ann -> Bool) -> Errors
errUndeclaredInvalid dcl (id,use) pred =
    case dcl of
        Nothing  -> [toError use "identifier '" ++ id ++ "' is not declared"]
        (Just s) -> if pred s then [] else
                        [toError use "identifier '" ++ id ++ "' is invalid"]

-------------------------------------------------------------------------------

expr :: (Ann ann) => [Stmt ann] -> Exp ann -> (Maybe Type,Errors)
expr ids e@(Read _ id) = if id == "_INPUT" then (Just ["Int"],[]) else
                            (tp, errUndeclaredInvalid dcl (id,e) isVar)
                         where
                            dcl = find' id ids
                            tp  = case dcl of
                                    Nothing -> Nothing
                                    Just s  -> Just (getType s)
expr ids (Umn _ e)      = expr ids e
expr ids (Add _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids (Sub _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids (Mul _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids (Div _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids (Equ _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids (Lte _ e1 e2)  = (Just ["Int"], (snd $ expr ids e1) ++ (snd $ expr ids e2))
expr ids _              = (Just ["Int"], [])
