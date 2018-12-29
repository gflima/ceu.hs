module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type
import Ceu.Grammar.Ann      (Ann(getType,toError,toErrorTypes))
import Ceu.Grammar.Ann.Type
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt hiding (getAnn)

go :: (Ann a) => (Stmt a) -> (Errors, Stmt Type)
go p = stmt [] p

stmt :: (Ann a) => [Stmt a] -> Stmt a -> (Errors, Stmt Type)

stmt ids s@(Var  z id tp p)  = ((errDeclared ids (id,z)) ++ es, Var  TypeB id tp p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Inp  z id p)     = ((errDeclared ids (id,z)) ++ es, Inp  TypeB id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Out  z id p)     = ((errDeclared ids (id,z)) ++ es, Out  TypeB id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Evt  z id p)     = ((errDeclared ids (id,z)) ++ es, Evt  TypeB id p')
                               where (es,p') = stmt (s:ids) p
stmt ids s@(Func z id tp p)  = ((errDeclared ids (id,z)) ++ es, Func TypeB id tp p')
                               where (es,p') = stmt (s:ids) p

stmt ids (Write z id exp)    = (es1 ++ es2 ++ es3, Write TypeB id exp')
                               where
                                (es1,tp1)  = fff id ids z isVar
                                (es2,exp') = expr ids exp
                                es3        = if isTypeB tp1 || isTypeB tp then
                                                []
                                             else
                                                toErrorTypes z tp1 tp
                                             where tp = getType $ getAnn exp'

stmt ids (AwaitInp z id)     = (fst $ fff id ids z isInp, AwaitInp TypeB id)
stmt ids (EmitExt  z id exp) = ((fst $ fff id ids z isExt) ++ es, EmitExt TypeB id exp')
                                 where
                                    (es,exp') = case exp of
                                        Nothing -> ([],Nothing)
                                        Just e  -> (es,Just exp') where (es,exp') = expr ids e
stmt ids (AwaitEvt z id)     = (fst $ fff id ids z isEvt, AwaitEvt TypeB id)
stmt ids (EmitEvt  z id)     = (fst $ fff id ids z isEvt, EmitEvt  TypeB id)

stmt ids (If  z exp p1 p2)   = (ese ++ es ++ es1 ++ es2, If TypeB exp' p1' p2')
                               where
                                (ese,exp') = expr ids exp
                                es = toErrorTypes z (Type1 "Bool") (getType $ getAnn exp')
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq _ p1 p2)       = (es1++es2, Seq TypeB p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop _ p)          = (es, Loop TypeB p')
                               where
                                (es,p') = stmt ids p
stmt ids (Every z evt p)     = ((fst $ fff evt ids z isInpEvt) ++ es, Every TypeB evt p')
                               where
                                (es,p') = stmt ids p
stmt ids (Par _ p1 p2)       = (es1++es2, Par TypeB p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Pause z id p)      = ((fst $ fff id ids z isVar) ++ es, Pause TypeB id p')
                               where
                                (es,p') = stmt ids p
stmt ids (Fin _ p)           = (es, Fin TypeB p')
                               where
                                (es,p') = stmt ids p
stmt ids (Trap _ p)          = (es, Trap TypeB p')
                               where
                                (es,p') = stmt ids p
stmt _   (Escape _ n)        = ([], Escape TypeB n)
stmt _   (Nop    _)          = ([], Nop TypeB)
stmt _   (Halt   _)          = ([], Halt TypeB)
stmt ids (RawS   _ raws)     = (es, RawS TypeB raws')
                               where
                                (es,raws') = fold_raws ids raws
stmt _   (Error  _ msg)      = ([], Error TypeB msg)

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

fff :: (Ann b) => String -> [Stmt a] -> b -> (Stmt a -> Bool) -> (Errors, Type)
fff id ids z pred =
    case dcl of
        Nothing -> ([toError z "identifier '" ++ id ++ "' is not declared"], TypeB)
        Just s  -> if pred s then
                    ([], retType dcl)
                   else
                    ([toError z "identifier '" ++ id ++ "' is invalid"], TypeB)
    where
        dcl = find' id ids

        retType :: Maybe (Stmt a) -> Type
        retType Nothing                           = TypeB
        retType (Just (Var _ _ tp _))             = tp
        retType (Just (Func _ _ (TypeF inp _) _)) = inp       -- input type (params)

-------------------------------------------------------------------------------


isTypeB TypeB = True
isTypeB _     = False

fold_raws :: (Ann a) => [Stmt a] -> [RawAt a] -> (Errors, [RawAt Type])
fold_raws ids raws = foldr f ([],[]) raws where
                        f (RawAtE exp) (l1,l2) = (es'++l1, (RawAtE exp'):l2)
                                                 where
                                                    exp' :: Exp Type
                                                    (es',exp') = expr ids exp
                        f (RawAtS str) (l1,l2) = (l1, (RawAtS str):l2)

-------------------------------------------------------------------------------

expr :: (Ann a) => [Stmt a] -> Exp a -> (Errors, Exp Type)

expr ids (RawE  _ raws)  = (es, RawE TypeT raws')
                           where
                            (es,raws') = fold_raws ids raws
expr _   (Const _ val)   = ([], Const (Type1 "Int") val)
expr _   (Unit _)        = ([], Unit Type0)

expr ids (Tuple _ exps)  = (es, Tuple tps' exps')
                           where
                            rets :: [(Errors,Exp Type)]
                            rets  = map (\e -> expr ids e) exps
                            es    = concat $ map fst rets
                            exps' = map snd rets
                            tps'  = TypeN (map (getType.getAnn) exps')

expr ids (Read z id)     = if id == "_INPUT" then
                            ([], Read (Type1 "Int") id)
                           else
                            (es, Read tp' id)
                           where
                            (es,tp') = fff id ids z isVar

expr ids (Call z id exp) = (es1++es2++es3, Call tp id exp')
                           where
                            (es1,tp1)  = fff id ids z isFunc
                            (es2,exp') = expr ids exp
                            es3        = if isTypeB tp1 || isTypeB tp then
                                            []
                                         else
                                            toErrorTypes z tp1 tp
                                         where tp = getType $ getAnn exp'
                            tp = case find' id ids of
                                    Just (Func _ _ (TypeF _ tp') _) -> tp'
                                    otherwise                       -> TypeB
