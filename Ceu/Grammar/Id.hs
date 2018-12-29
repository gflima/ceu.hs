module Ceu.Grammar.Id where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann(toError, toErrorTypes))
import Ceu.Grammar.Type
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

check :: (Ann a) => (Stmt a) -> Errors
check p = stmt [] p

stmt :: (Ann a) => [Stmt a] -> Stmt a -> Errors

stmt ids s@(Var z id _ p)    = (errDeclared ids (id,z)) ++ (stmt (s:ids) p)
stmt ids s@(Inp z id p)      = (errDeclared ids (id,z)) ++ (stmt (s:ids) p)
stmt ids s@(Out z id p)      = (errDeclared ids (id,z)) ++ (stmt (s:ids) p)
stmt ids s@(Evt z id p)      = (errDeclared ids (id,z)) ++ (stmt (s:ids) p)
stmt ids s@(Func z id _ p)   = (errDeclared ids (id,z)) ++ (stmt (s:ids) p)

stmt ids (Write z id exp)    = es1 ++ es2 ++ es3
                              where
                                (tp1,es1) = fff id ids z isVar
                                (tp2,es2) = expr ids exp
                                es3       = if isTypeB tp1 || isTypeB tp2 then
                                                []
                                            else
                                                toErrorTypes z tp1 tp2

stmt ids (AwaitInp z id)     = snd  $ fff id ids z isInp
stmt ids (EmitExt  z id exp) = (snd $ fff id ids z isExt) ++ es
                                 where
                                    es = case exp of
                                        Nothing -> []
                                        Just e  -> es where (_,es) = expr ids e
stmt ids (AwaitEvt z id)     = snd $ fff id ids z isEvt
stmt ids (EmitEvt  z id)     = snd $ fff id ids z isEvt

stmt ids (If  z exp p1 p2) = es1 ++ es2 ++ (stmt ids p1) ++ (stmt ids p2)
                               where
                                (tp,es1) = (expr ids exp)
                                es2 = toErrorTypes z (Type1 "Bool") tp
stmt ids (Seq _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Loop _ p)        = (stmt ids p)
stmt ids (Every z evt p)   = (snd $ fff evt ids z isInpEvt) ++ (stmt ids p)
stmt ids (Par _ p1 p2)     = (stmt ids p1) ++ (stmt ids p2)
stmt ids (Pause z id p)    = (snd $ fff id ids z isVar) ++ (stmt ids p)
stmt ids (Fin _ p)         = (stmt ids p)
stmt ids (Trap _ p)        = (stmt ids p)
stmt ids p                 = []

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

isFunc (Func _ _ _ _) = True
isFunc _              = False

getId :: Stmt a -> String
getId (Var _ id _ _)    = id
getId (Inp _ id _)      = id
getId (Out _ id _)      = id
getId (Evt _ id _)      = id
getId (Func _ id _ _)   = id

find' :: String -> [Stmt a] -> Maybe (Stmt a)
find' id ids = find (\s -> getId s == id) ids

errDeclared :: (Ann b) => [Stmt a] -> (String, b) -> Errors
errDeclared ids (id,z) =
    if (take 2 id == "__") then [] else    -- nested par/and (__and)
        case find' id ids of
            Nothing   -> []
            s         -> [toError z "identifier '" ++ id ++ "' is already declared"]

fff :: (Ann b) => String -> [Stmt a] -> b -> (Stmt a -> Bool) -> (Type, Errors)
fff id ids z pred =
    case dcl of
        Nothing -> (TypeB, [toError z "identifier '" ++ id ++ "' is not declared"])
        Just s  -> if pred s then
                    (retType dcl, [])
                   else
                    (TypeB, [toError z "identifier '" ++ id ++ "' is invalid"])
    where
        dcl = find' id ids

        retType :: Maybe (Stmt a) -> Type
        retType Nothing                           = TypeB
        retType (Just (Var _ _ tp _))             = tp
        retType (Just (Func _ _ (TypeF inp _) _)) = inp       -- input type (params)

-------------------------------------------------------------------------------


isTypeB TypeB = True
isTypeB _     = False

-------------------------------------------------------------------------------

expr :: (Ann a) => [Stmt a] -> Exp a -> (Type,Errors)

expr _ (RawE  _ _)  = (TypeT, [])
expr _ (Const _ _)  = ((Type1 "Int"), [])
expr _ (Unit _)     = (Type0, [])

expr ids e@(Tuple _ exps) = (tps, es)
                            where
                                rets :: [(Type,Errors)]
                                rets = map (\e -> expr ids e) exps
                                tps  = if elem TypeB tps' then TypeB else TypeN tps'
                                tps' = map (\(tp,_) -> tp) rets
                                es   = concat $ map (\(_,es) -> es) rets

expr ids (Read z id) = if id == "_INPUT" then
                        ((Type1 "Int"),[])
                       else
                        fff id ids z isVar

expr ids (Call z id exp) = (tp, es1++es2++es3)
                            where
                                (tp1,es1) = fff id ids z isFunc
                                (tp2,es2) = expr ids exp
                                es3       = if isTypeB tp1 || isTypeB tp2 then
                                                []
                                            else
                                                toErrorTypes z tp1 tp2
                                tp = case find' id ids of
                                        Just (Func _ _ (TypeF _ tp') _) -> tp'
                                        otherwise                       -> TypeB
