module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Ann
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Class z id vars ifc p) = ((errDeclared "typeclass" ids (id,z)) ++ es1 ++ es2,
                                        Class z id vars ifc' p')
                                        where
                                            (es1,ifc') = stmt (traceShowId ids) (traceShowId ifc)
                                            (es2,p')   = stmt (s:ids) p

stmt ids s@(Data z id [] cons abs p) = ((errDeclared "type" ids (tp12str id,z)) ++ es, Data z id [] cons abs p')
                                    where (es,p') = stmt (s:ids) p
stmt ids s@(Data z id vars cons abs p) = error "not implemented"

stmt ids s@(Var  z id tp p)  = (es_data ++ es_id ++ es, Var z id tp p')
                               where
                                es_data = concatMap f $ map (\id->(id, find (isData id) ids)) $ get1s tp
                                f (id, Nothing) = [toError z "type '" ++ (tp12str id) ++ "' is not declared"]
                                f (_,  Just _)  = []

                                es_id   = errDeclared "variable" ids (id,z)
                                (es,p') = stmt (s:ids) p
stmt ids s@(Inp  z id p)     = ((errDeclared "input" ids (id,z)) ++ es, Inp  z id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Out  z id tp p)  = ((errDeclared "output" ids (id,z)) ++ es, Out  z id tp p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Evt  z id p)     = ((errDeclared "event" ids (id,z)) ++ es, Evt  z id p')
                               where (es,p') = stmt (s:ids) p

stmt ids s@(Func z id tp p)  = (es ++ es', Func z id tp p') where
    (es, (es',p')) = case find (isFunc id) ids of
        Nothing               -> ([],                    stmt (s:ids) p)
        Just (Func _ _ tp' _) -> (toErrorTypes z tp' tp, stmt ids p)

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
                                es3        = toErrorTypes z tps_loc (type_ $ getAnn exp')

stmt ids s@(AwaitInp z id) = (es,s) where
                             es = case find (isInp id) ids of
                                Nothing   -> [toError z "input '" ++ id ++ "' is not declared"]
                                otherwise -> []

stmt ids (EmitExt z id exp) = (es1++es2++es3, EmitExt z id exp')
                              where
                                (tp,es1) = case find (isOut id) ids of
                                    Nothing ->
                                        (TypeT, [toError z "output '" ++ id ++ "' is not declared"])
                                    Just (Out _ _ tp _) ->
                                        (tp, [])
                                (es2,exp') = expr ids exp
                                es3        = toErrorTypes z tp (type_ $ getAnn exp')

stmt ids s@(AwaitEvt z id)   = (es, s) where
                                es = case find (isEvt id) ids of
                                        Nothing -> [toError z "event '" ++ id ++ "' is not declared"]
                                        Just _  -> []

stmt ids s@(EmitEvt  z id)   = (es, s) where
                                es = case find (isEvt id) ids of
                                        Nothing -> [toError z "event '" ++ id ++ "' is not declared"]
                                        Just _  -> []

stmt ids (If  z exp p1 p2)   = (ese ++ es ++ es1 ++ es2, If z exp' p1' p2')
                               where
                                (ese,exp') = expr ids exp
                                es = toErrorTypes z (Type1 ["Bool"]) (type_ $ getAnn exp')
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq z p1 p2)       = (es1++es2, Seq z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)          = (es, Loop z p')
                               where
                                (es,p') = stmt ids p

stmt ids (Every z evt p)     = (es1++es2, Every z evt p')
                               where
                                (es2,p') = stmt ids p
                                es1 = case find (isInpEvt evt) ids of
                                        Nothing -> [toError z "event '" ++ evt ++ "' is not declared"]
                                        Just _  -> []

stmt ids (Par z p1 p2)       = (es1++es2, Par z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2

stmt ids (Pause z id p)      = (es1++es2, Pause z id p')
                               where
                                (es2,p') = stmt ids p
                                es1 = case find (isVar id) ids of
                                        Nothing -> [toError z "variable '" ++ id ++ "' is not declared"]
                                        Just _  -> []

stmt ids (Fin z p)           = (es, Fin z p')
                               where
                                (es,p') = stmt ids p
stmt ids (Trap z p)          = (es, Trap z p')
                               where
                                (es,p') = stmt ids p
stmt _   (Escape z n)        = ([], Escape z n)
stmt _   (Nop    z)          = ([], Nop z)
stmt _   (Halt   z)          = ([], Halt z)
stmt ids (RawS   z raws)     = (es, RawS z raws')
                               where
                                (es,raws') = fold_raws ids raws
stmt _   (Error  z msg)      = ([], Error z msg)

-------------------------------------------------------------------------------

isData id (Data _ id' _ _ _ _) = (id == id')
isData _  _                    = False

isVar  id (Var _ id' _ _) = (id == id')
isVar  _  _               = False

isInp  id (Inp _ id' _)   = (id == id')
isInp  _  _               = False

isOut  id (Out _ id' _ _) = (id == id')
isOut  _  _               = False

isEvt  id (Evt _ id' _)   = (id == id')
isEvt  _  _               = False

isFunc id (Func _ id' _ _)= True
isFunc _  _               = False

isInpEvt id s = isInp id s || isEvt id s

isAny id (Data _ id' _ _ _ _) = id == tp12str id'
isAny id (Var  _ id' _ _)     = id == id'
isAny id (Inp  _ id' _)       = id == id'
isAny id (Out  _ id' _ _)     = id == id'
isAny id (Evt  _ id' _)       = id == id'
isAny id (Func _ id' _ _)     = id == id'

errDeclared :: String -> [Stmt] -> (String, Ann) -> Errors
errDeclared str ids (id,z) =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny id) ids of
            Nothing   -> []
            _         -> [toError z str ++ " '" ++ id ++ "' is already declared"]

-------------------------------------------------------------------------------


isTypeB TypeB = True
isTypeB _     = False

fold_raws :: [Stmt] -> [RawAt] -> (Errors, [RawAt])
fold_raws ids raws = foldr f ([],[]) raws where
                        f (RawAtE exp) (l1,l2) = (es'++l1, (RawAtE exp'):l2)
                                                 where
                                                    (es',exp') = expr ids exp
                        f (RawAtS str) (l1,l2) = (l1, (RawAtS str):l2)

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> (Errors, Exp)

expr ids (RawE  z raws)  = (es, RawE z{type_=TypeT} raws')
                           where
                            (es,raws') = fold_raws ids raws
expr _   (Const z val)   = ([], Const z{type_=Type1 ["Int"]} val)
expr _   (Unit z)        = ([], Unit  z{type_=Type0})

expr ids (Cons  z id)    = (es, Cons  z{type_=(Type1 id)} id)
    where
        es = case find (isData id) ids of
            Nothing                    -> [toError z "type '" ++ tp12str id ++ "' is not declared"]
            Just (Data _ _ _ _ True _) -> [toError z "type '" ++ tp12str id ++ "' is abstract"]
            otherwise                  -> []

expr ids (Tuple z exps)  = (es, Tuple z{type_=tps'} exps')
                           where
                            rets :: [(Errors,Exp)]
                            rets  = map (\e -> expr ids e) exps
                            es    = concat $ map fst rets
                            exps' = map snd rets
                            tps'  = TypeN (map (type_.getAnn) exps')

expr ids (Read z id)     = if id == "_INPUT" then
                            ([], Read z{type_=Type1 ["Int"]} id)
                           else
                            (es, Read z{type_=tp'} id)
                           where
                            (tp',es) = case find (isVar id) ids of
                                        Nothing               -> (TypeT, [toError z "variable '" ++ id ++ "' is not declared"])
                                        (Just (Var _ _ tp _)) -> (tp,    [])

expr ids (Call z id exp) = (es++es_exp, Call z{type_=tp_out} id exp')
                           where
                            (es_exp, exp') = expr ids exp
                            tp_exp' = type_ $ getAnn exp'

                            (tp_out,es) = case find (isFunc id) ids of
                                            Nothing ->
                                                (TypeT, [toError z "function '" ++ id ++ "' is not declared"])
                                            (Just (Func _ _ (TypeF inp out) _)) ->
                                                case toErrorTypes z inp tp_exp' of
                                                    [] -> (instType out (inp,tp_exp'), [])
                                                    x  -> (TypeT,                      x)
