module Ceu.Grammar.Id where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (Ann ann) => (Stmt ann) -> Errors
check p = stmt [] p

stmt :: (Ann ann) => [Stmt ann] -> Stmt ann -> Errors

stmt ids s@(Var _ id _ p)    = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Inp _ id p)      = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Out _ id p)      = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(Evt _ id p)      = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)
stmt ids s@(CodI _ id _ _ p) = (errDeclared ids (id,s)) ++ (stmt (s:ids) p)

stmt ids s@(Write _ id exp) = es1 ++ es2 ++ es3
                              where
                                (tp1,es1) = fff id ids s isVar
                                (tp2,es2) = expr ids exp
                                es3       = if isTypeB tp1 || isTypeB tp2 then
                                                []
                                            else
                                                checkTypesErrs s tp1 tp2

stmt ids s@(AwaitInp _ id)     = snd $ fff id ids s isInp
stmt ids s@(EmitExt  _ id exp) = (snd $ fff id ids s isExt) ++ es
                                 where
                                    es = case exp of
                                        Nothing -> []
                                        Just e  -> es where (_,es) = expr ids e
stmt ids s@(AwaitEvt _ id)     = snd $ fff id ids s isEvt
stmt ids s@(EmitEvt  _ id)     = snd $ fff id ids s isEvt

stmt ids s@(If  _ exp p1 p2) = es1 ++ es2 ++ (stmt ids p1) ++ (stmt ids p2)
                               where
                                (tp,es1) = (expr ids exp)
                                es2 = checkTypesErrs s (Type1 "Bool") tp
stmt ids (Seq _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Loop _ p)        = (stmt ids p)
stmt ids s@(Every _ evt p) = (snd $ fff evt ids s isInpEvt) ++ (stmt ids p)
stmt ids (Par _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids s@(Pause _ id p)  = (snd $ fff id ids s isVar) ++ (stmt ids p)
stmt ids (Fin _ p)         = (stmt ids p)
stmt ids (Trap _ p)        = (stmt ids p)
stmt ids p                 = []

-------------------------------------------------------------------------------

getType :: Maybe (Stmt ann) -> Type
getType Nothing                  = TypeB
getType (Just (Var _ _ tp _))    = tp
getType (Just (CodI _ _ tp _ _)) = tp        -- input type (params)

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

isCodI (CodI _ _ _ _ _) = True
isCodI _                = False

getId :: Stmt ann -> String
getId (Var _ id _ _)    = id
getId (Inp _ id _)      = id
getId (Out _ id _)      = id
getId (Evt _ id _)      = id
getId (CodI _ id _ _ _) = id

find' :: String -> [Stmt ann] -> Maybe (Stmt ann)
find' id ids = find (\s -> getId s == id) ids

errDeclared :: (INode a) => [Stmt ann] -> (String,a) -> Errors
errDeclared ids (id,dcl) =
    if (take 2 id == "__") then [] else    -- nested par/and (__and)
        case find' id ids of
            Nothing   -> []
            s         -> [toError dcl "identifier '" ++ id ++ "' is already declared"]

fff :: (INode a) => String -> [Stmt ann] -> a -> (Stmt ann -> Bool) -> (Type, Errors)
fff id ids use pred =
    case dcl of
        Nothing -> (TypeB, [toError use "identifier '" ++ id ++ "' is not declared"])
        Just s  -> if pred s then
                    (getType dcl, [])
                   else
                    (TypeB, [toError use "identifier '" ++ id ++ "' is invalid"])
    where
        dcl = find' id ids

isTypeB TypeB = True
isTypeB _     = False

-------------------------------------------------------------------------------

expr :: (Ann ann) => [Stmt ann] -> Exp ann -> (Type,Errors)

expr _ (Const _ _)  = ((Type1 "Int"), [])
expr _ (Unit _)     = (Type0, [])

expr ids e@(Read _ id) = if id == "_INPUT" then
                            ((Type1 "Int"),[])
                         else
                            fff id ids e isVar

expr ids e@(Call _ id exp) = (tp, es1++es2++es3)
                             where
                                (tp1,es1) = fff id ids e isCodI
                                (tp2,es2) = expr ids exp
                                es3       = if isTypeB tp1 || isTypeB tp2 then
                                                []
                                            else
                                                checkTypesErrs e tp1 tp2
                                tp = case find' id ids of
                                        Just (CodI _ _ _ tp' _) -> tp'
                                        otherwise               -> TypeB

expr ids e@(Tuple _ exps) = (TypeN tps, es)
                            where
                                rets :: [(Type,Errors)]
                                rets = map (\e -> expr ids e) exps
                                tps  = map (\(tp,_) -> tp) rets
                                es   = concat $ map (\(_,es) -> es) rets

expr _ _ = error "TODO"
