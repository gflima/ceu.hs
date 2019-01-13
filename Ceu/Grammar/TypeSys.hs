module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Ann
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p

-------------------------------------------------------------------------------

isClass id (Class _ id' _ _ _)  = (id == id')
isClass _  _                    = False

isData  id (Data _ id' _ _ _ _) = (id == id')
isData  _  _                    = False

isVar   id (Var _ id' _ _)      = (id == id')
isVar   _  _                    = False

isFunc  id (Func _ id' _ _)     = (id == id')
isFunc  _  _                    = False

isAny id s = isClass id s || isData id s || isVar  id s || isFunc id s

errDeclared :: Ann -> String -> String -> [Stmt] -> Errors
errDeclared z str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny id) ids of
            Nothing  -> []
            (Just _) -> [toError z str ++ " '" ++ id ++ "' is already declared"]

getErrsTypesDeclared :: Ann -> Type -> [Stmt] -> Errors
getErrsTypesDeclared z tp ids = concatMap aux $ map (\id->(id, find (isData id) ids)) $ get1s tp
    where
        aux (id, Nothing) = [toError z "type '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

getErrsTypesMatch :: Ann -> Type -> Type -> Errors
getErrsTypesMatch z t1 t2 = if t1 `isSupOf` t2 then [] else
                                [toError z "types do not match : " ++ typeShow t1 ++ " :> " ++ typeShow t2]

call :: Ann -> [Stmt] -> ID_Func -> Exp -> (Errors, Type, Exp)
call z ids id exp = (es++es_exp, tp_out, exp')
    where
        (es_exp, exp') = expr ids exp
        tp_exp' = type_ $ getAnn exp'

        (tp_out,es) = case find (isFunc id) (expandInsts ids) of
                        Nothing ->
                            (TypeT, [toError z "function '" ++ id ++ "' is not declared"])
                        (Just (Func _ _ (TypeF inp out) _)) ->
                            case getErrsTypesMatch z inp tp_exp' of
                                [] -> (instType out (inp,tp_exp'), [])
                                x  -> (TypeT,                      x)

classinst2ids :: Stmt -> [Stmt]
classinst2ids p = case p of
    (Class _ _ _ ifc _) -> aux ifc
    (Inst  _ _ _ imp _) -> aux imp
    where
        aux (Nop _)             = []
        aux s@(Func  _ _ _ p)   = s : aux p

expandInsts :: [Stmt] -> [Stmt]
expandInsts [] = []
expandInsts (s@(Inst _ _ _ _ _) : l) = classinst2ids s ++ expandInsts l
expandInsts (s : l) = s : expandInsts l

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Class z id [var] ifc p) = ((errDeclared z "typeclass" id ids) ++ es1 ++ es2,
                                        Class z id [var] ifc' p')
                                        where
                                            (es1,ifc') = stmt ids ifc
                                            (es2,p')   = stmt (s:ids) p

stmt ids (Class _ _ vars _ _) = error "not implemented: multiple vars"

stmt ids s@(Inst z id [tp] imp p) = (es0 ++ es1 ++ es2 ++ es3, Inst z id [tp] imp' p')
    where
        (es2,imp') = stmt (filter (not . isClass id) ids) imp -- prevent clashes w/ own class
        (es3,p')   = stmt (s:ids) p

        -- check if this instance is already declared
        es1 = case find isSameInst ids of
            Nothing  -> []
            (Just _) -> [toError z "instance '" ++ id ++ " (" ++ intercalate "," [tp] ++ ")' is already declared"]
        isSameInst (Inst _ id' [tp'] _ _) = (id==id' && [tp]==[tp'])
        isSameInst _                     = False

        -- check if class exists
        -- compares class vs instance function by function in order
        es0 = case find (isClass id) ids of
            Nothing                     -> [toError z "typeclass '" ++ id ++ "' is not declared"]
            Just (Class _ _ [var] ifc _) -> compares ifc imp where
                compares (Func _ id1 tp1 p1) (Func  _ id2 tp2   p2) =
                    (names id1 id2) ++ (supOf tp1 tp2) ++ (instOf var tp1 tp2) ++ (compares p1 p2)
                compares (Nop _) (Nop _) = []

        -- check if function names are the same
        names id1 id2 | id1==id2  = []
                      | otherwise = [toError z "names do not match : " ++ id1 ++ " :> " ++ id2]

        -- check if function types match
        supOf tp1 tp2 | tp1 `isSupOf` tp2 = []
                      | otherwise         = [toError z "types do not match : " ++
                                             typeShow tp1 ++ " :> " ++ typeShow tp2]

        -- check if (Inst tps) match (Class vars) in all functions
        instOf var tp1 tp2 = case instType (TypeV var) (tp1,tp2) of
                                (Type1 tp') | tp==tp'   -> []
                                            | otherwise -> ["types do not match : " ++
                                                            tp ++ " :> " ++ tp']

stmt ids (Inst _ _ tps _ _) = error "not implemented: multiple types"

stmt ids s@(Data z id [] cons abs p) = ((errDeclared z "type" id ids) ++ es, Data z id [] cons abs p')
                                    where (es,p') = stmt (s:ids) p
stmt ids s@(Data z id vars cons abs p) = error "not implemented"

stmt ids s@(Var  z id tp p)  = (es_data ++ es_id ++ es, Var z id tp p')
                               where
                                es_data = getErrsTypesDeclared z tp ids
                                es_id   = errDeclared z "variable" id ids
                                (es,p') = stmt (s:ids) p

stmt ids s@(Func z id tp p)  = (es_data ++ es_dcl ++ es ++ es', Func z id tp p') where
    (es, (es',p')) = case find (isFunc id) ids of
        Nothing               -> ([],                    stmt (s:ids) p)
        Just (Func _ _ tp' _) -> (getErrsTypesMatch z tp' tp, stmt ids p)
    es_data = getErrsTypesDeclared z tp ids

    -- check if clashes with functions in classes
    es_dcl = errDeclared z "function" id ids'
    ids' = concatMap classinst2ids $ filter isClass' ids
    isClass' (Class _ _ _ _ _) = True
    isClass' _                 = False

stmt ids s@(FuncI z id tp imp p) = (es1++es2, FuncI z id tp imp' p')
                                   where
                                    (es1,imp') = stmt ids imp
                                    (es2,p')   = stmt ids p

stmt ids (Write z loc exp)   = (es1 ++ es2 ++ es3, Write z loc exp')
                               where
                                (tps_loc, es1) = aux loc
                                aux :: Loc -> (Type, Errors)
                                aux LAny       = (TypeT, [])
                                aux (LVar var) = case find (isVar var) ids of
                                                    Nothing ->
                                                        (TypeT, [toError z "variable '" ++ var ++ "' is not declared"])
                                                    (Just (Var _ _ tp _)) ->
                                                        (tp,    [])
                                aux (LTuple l) = (TypeN tps, es) where
                                                 l' :: [(Type,Errors)]
                                                 l' = map aux l
                                                 (tps,es) = foldr cat ([],[]) l'
                                                 cat (tp,es1) (tps,es2) = (tp:tps, es1++es2)

                                (es2,exp') = expr ids exp
                                es3        = getErrsTypesMatch z tps_loc (type_ $ getAnn exp')

stmt ids (CallS z id exp)   = (es, CallS z id exp') where
                              (es,_,exp') = call z ids id exp

stmt ids (If  z exp p1 p2)   = (ese ++ es ++ es1 ++ es2, If z exp' p1' p2')
                               where
                                (ese,exp') = expr ids exp
                                es = getErrsTypesMatch z (Type1 "Bool") (type_ $ getAnn exp')
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq z p1 p2)       = (es1++es2, Seq z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2

stmt _   (Nop    z)          = ([], Nop z)

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> (Errors, Exp)

expr _   (Const z val)   = ([], Const z{type_=Type1 "Int"} val)
expr _   (Unit z)        = ([], Unit  z{type_=Type0})

expr ids (Cons  z id)    = (es, Cons  z{type_=(Type1 id)} id)
    where
        es = case find (isData id) ids of
            Nothing                    -> [toError z "type '" ++ id ++ "' is not declared"]
            Just (Data _ _ _ _ True _) -> [toError z "type '" ++ id ++ "' is abstract"]
            otherwise                  -> []

expr ids (Tuple z exps)  = (es, Tuple z{type_=tps'} exps')
                           where
                            rets :: [(Errors,Exp)]
                            rets  = map (\e -> expr ids e) exps
                            es    = concat $ map fst rets
                            exps' = map snd rets
                            tps'  = TypeN (map (type_.getAnn) exps')

expr ids (Read z id)     = if id == "_INPUT" then
                            ([], Read z{type_=Type1 "Int"} id)
                           else
                            (es, Read z{type_=tp'} id)
                           where
                            (tp',es) = case find (isVar id) ids of
                                        Nothing               -> (TypeT, [toError z "variable '" ++ id ++ "' is not declared"])
                                        (Just (Var _ _ tp _)) -> (tp,    [])

expr ids (Call z id exp) = (es, Call z{type_=tp_out} id exp') where
                           (es, tp_out, exp') = call z ids id exp
