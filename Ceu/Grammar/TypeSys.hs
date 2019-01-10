module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find)
import Data.Maybe (isJust)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Ann
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Data z id []   ors p) = ((errDeclared ids (id,z)) ++ es, Data z id [] ors p')
                                    where (es,p') = stmt (s:ids) p
stmt ids s@(Data z id vars ors p) = error "not implemented"

stmt ids s@(Var  z id tp p)  = (es_data ++ es_id ++ es, Var z id tp p')
                               where
                                es_data = concatMap (fst . (fff ids z isData)) (get1s tp)
                                es_id   = errDeclared ids (id,z)
                                (es,p') = stmt (s:ids) p
stmt ids s@(Inp  z id p)     = ((errDeclared ids (id,z)) ++ es, Inp  z id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Out  z id tp p)  = ((errDeclared ids (id,z)) ++ es, Out  z id tp p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Evt  z id p)     = ((errDeclared ids (id,z)) ++ es, Evt  z id p')
                               where (es,p') = stmt (s:ids) p

stmt ids s@(Func z id tp p)  = (es ++ es', Func z id tp p') where
    (es, (es',p')) = case find' id ids of
        Nothing               -> ([],                    stmt (s:ids) p)
        Just (Func _ _ tp' _) -> (toErrorTypes z tp' tp, stmt ids p)

stmt ids s@(FuncI z id tp imp p) = (es1++es2, FuncI z id tp imp' p')
                                   where
                                    (es1,imp') = stmt ids imp
                                    (es2,p')   = stmt ids p

stmt ids (Write z loc exp)   = (es1 ++ es2 ++ es3, Write z loc exp')
                               where
                                (es1,tps_loc)  = aux loc
                                aux :: Loc -> (Errors,Type)
                                aux LAny       = ([],TypeT)
                                aux (LVar var) = fff ids z isVar var
                                aux (LTuple l) = (es, TypeN tps) where
                                                 l' :: [(Errors,Type)]
                                                 l' = map aux l
                                                 (es,tps) = foldr cat ([],[]) l'
                                                 cat (es1,tp) (es2,tps) = (es1++es2, tp:tps)

                                (es2,exp') = expr ids exp
                                es3        = toErrorTypes z tps_loc (type_ $ getAnn exp')

stmt ids (AwaitInp z id)     = (fst $ fff ids z isInp id, AwaitInp z id)
stmt ids (EmitExt  z id exp) = (es1++es2++es3, EmitExt z id exp')
                                 where
                                    (es1,tp)   = fff ids z isOut id
                                    (es2,exp') = expr ids exp
                                    es3        = toErrorTypes z tp (type_ $ getAnn exp')
stmt ids (AwaitEvt z id)     = (fst $ fff ids z isEvt id, AwaitEvt z id)
stmt ids (EmitEvt  z id)     = (fst $ fff ids z isEvt id, EmitEvt  z id)

stmt ids (If  z exp p1 p2)   = (ese ++ es ++ es1 ++ es2, If z exp' p1' p2')
                               where
                                (ese,exp') = expr ids exp
                                es = toErrorTypes z (Type1 "Bool") (type_ $ getAnn exp')
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq z p1 p2)       = (es1++es2, Seq z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)          = (es, Loop z p')
                               where
                                (es,p') = stmt ids p
stmt ids (Every z evt p)     = ((fst $ fff ids z isInpEvt evt) ++ es, Every z evt p')
                               where
                                (es,p') = stmt ids p
stmt ids (Par z p1 p2)       = (es1++es2, Par z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Pause z id p)      = ((fst $ fff ids z isVar id) ++ es, Pause z id p')
                               where
                                (es,p') = stmt ids p
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

isData (Data _ _ _ _ _) = True
isData _                = False
isVar  (Var _ _ _ _)    = True
isVar  _                = False
isOut  (Out _ _ _ _)    = True
isOut  _                = False
isInp  (Inp _ _ _)      = True
isInp  _                = False
isEvt  (Evt _ _ _)      = True
isEvt  _                = False
isFunc (Func _ _ _ _)   = True
isFunc _                = False
isInpEvt (Inp _ _ _)    = True
isInpEvt (Evt _ _ _)    = True
isInpEvt _              = False

getId :: Stmt -> String
getId (Data _ id _ _ _) = id
getId (Var  _ id _ _)   = id
getId (Inp  _ id _)     = id
getId (Out  _ id _ _)   = id
getId (Evt  _ id _)     = id
getId (Func _ id _ _)   = id

find' :: String -> [Stmt] -> Maybe Stmt
find' id ids = find (\s -> getId s == id) ids

errDeclared :: [Stmt] -> (String, Ann) -> Errors
errDeclared ids (id,z) =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find' id ids of
            Nothing   -> []
            _         -> [toError z "identifier '" ++ id ++ "' is already declared"]

fff :: [Stmt] -> Ann -> (Stmt -> Bool) -> String -> (Errors, Type)
fff ids z pred id =
    case dcl of
        Nothing -> ([toError z "identifier '" ++ id ++ "' is not declared"], TypeT) -- TypeT will prevent extra errors
        Just s  -> if pred s then
                    ([], getType dcl)
                   else
                    ([toError z "identifier '" ++ id ++ "' is invalid"], TypeT) -- TypeT will prevent extra errors
    where
        dcl = find' id ids

        -- TODO: move to Stmt.hs?
        getType :: Maybe Stmt -> Type
        getType Nothing                = TypeB
        getType (Just (Data _ _ _ _ _)) = TypeB     -- TODO: caller should use "errUndeclared"
        getType (Just (Var  _ _ tp _)) = tp
        getType (Just (Out  _ _ tp _)) = tp
        getType (Just (Func _ _ tp _)) = tp
        getType p                      = error (show p)

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
expr _   (Const z val)   = ([], Const z{type_=Type1 "Int"} val)
expr _   (Unit z)        = ([], Unit  z{type_=Type0})

expr ids (Cons  z id)    = (es, Cons  z{type_=tp} id)
    where
    ds = take 1 $ concatMap f ids
    f s@(Data _ _ _ (Just ors) _) = map (flip (,) s) $
                                        filter (\(DataOr (id',_))->id==id') ors
    f _                           = []

    (es,tp) = case ds of
        []                     -> ([toError z "identifier '" ++ id ++ "' is not declared"], TypeT)
        [(_, Data _ tp _ _ _)] -> ([], Type1 tp)

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
                            (es,tp') = fff ids z isVar id

expr ids (Call z id exp) = (es++es_exp, Call z{type_=tp_out} id exp')
                           where
                            (es_exp, exp') = expr ids exp
                            tp_exp' = type_ $ getAnn exp'

                            (es,tp_out) =
                                let (es',tp_func) = fff ids z isFunc id in
                                    case tp_func of
                                        TypeT -> (es', TypeT)    -- func not found
                                        TypeF inp out -> case toErrorTypes z inp tp_exp' of
                                            [] -> ([], instType out (inp,tp_exp'))
                                            x  -> (x, TypeT)
                                        tp -> error (show tp)
