module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Ann
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt hiding (getAnn)

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Var  z id tp p)  = ((errDeclared ids (id,z)) ++ es, Var  z id tp p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Inp  z id p)     = ((errDeclared ids (id,z)) ++ es, Inp  z id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Out  z id p)     = ((errDeclared ids (id,z)) ++ es, Out  z id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Evt  z id p)     = ((errDeclared ids (id,z)) ++ es, Evt  z id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Func z id tp p)  = ((errDeclared ids (id,z)) ++ es, Func z id tp p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(FuncI z id tp imp p) = (es, FuncI z id tp imp p')
                                    where (es,p') = stmt ids p

stmt ids (Write z id exp)    = (es1 ++ es2 ++ es3, Write z id exp')
                               where
                                (es1,tp1)  = fff id ids z isVar
                                (es2,exp') = expr ids exp
                                es3        = if isTypeB tp1 || isTypeB tp then
                                                []
                                             else
                                                toErrorTypes z tp1 tp
                                             where tp = type_ $ getAnn exp'

stmt ids (AwaitInp z id)     = (fst $ fff id ids z isInp, AwaitInp z id)
stmt ids (EmitExt  z id exp) = ((fst $ fff id ids z isExt) ++ es, EmitExt z id exp')
                                 where
                                    (es,exp') = case exp of
                                        Nothing -> ([],Nothing)
                                        Just e  -> (es,Just exp') where (es,exp') = expr ids e
stmt ids (AwaitEvt z id)     = (fst $ fff id ids z isEvt, AwaitEvt z id)
stmt ids (EmitEvt  z id)     = (fst $ fff id ids z isEvt, EmitEvt  z id)

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
stmt ids (Every z evt p)     = ((fst $ fff evt ids z isInpEvt) ++ es, Every z evt p')
                               where
                                (es,p') = stmt ids p
stmt ids (Par z p1 p2)       = (es1++es2, Par z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Pause z id p)      = ((fst $ fff id ids z isVar) ++ es, Pause z id p')
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

getId :: Stmt -> String
getId (Var  _ id _ _) = id
getId (Inp  _ id _)   = id
getId (Out  _ id _)   = id
getId (Evt  _ id _)   = id
getId (Func _ id _ _) = id

find' :: String -> [Stmt] -> Maybe Stmt
find' id ids = find (\s -> getId s == id) ids

errDeclared :: [Stmt] -> (String, Ann) -> Errors
errDeclared ids (id,z) =
    if (take 2 id == "__") then [] else    -- nested par/and (__and)
        case find' id ids of
            Nothing   -> []
            s         -> [toError z "identifier '" ++ id ++ "' is already declared"]

fff :: String -> [Stmt] -> Ann -> (Stmt -> Bool) -> (Errors, Type)
fff id ids z pred =
    case dcl of
        Nothing -> ([toError z "identifier '" ++ id ++ "' is not declared"], TypeT) -- TypeT will prevent extra errors
        Just s  -> if pred s then
                    ([], retType dcl)
                   else
                    ([toError z "identifier '" ++ id ++ "' is invalid"], TypeT) -- TypeT will prevent extra errors
    where
        dcl = find' id ids

        retType :: Maybe Stmt -> Type
        retType Nothing                = TypeB
        retType (Just (Var  _ _ tp _)) = tp
        retType (Just (Func _ _ tp _)) = tp

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
                            (es,tp') = fff id ids z isVar

expr ids (Call z id exp) = (es++es_exp, Call z{type_=tp_out} id exp')
                           where
                            (es_exp, exp') = expr ids exp
                            tp_exp' = type_ $ getAnn exp'

                            (es,tp_out) =
                                let (es',tp_func) = fff id ids z isFunc in
                                    case tp_func of
                                        TypeT -> (es', TypeT)    -- func not found
                                        TypeF inp out ->
                                            (toErrorTypes z inp tp_exp',
                                            instType out (inp,tp_exp'))
                                        tp -> error (show tp)
