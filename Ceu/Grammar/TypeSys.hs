module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate)
import Data.Maybe (isJust)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type as Type (Type(..), show', supOf, isSubOf, supOfErrors, instantiate, get1s)
import Ceu.Grammar.Ann
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p

-------------------------------------------------------------------------------

isClass f (Class _ id _ _ _)   = f id
isClass _  _                   = False

isInst  f (Inst  _ id _ _ _)   = f id
isInst  _  _                   = False

isData  f (Data  _ id _ _ _ _) = f id
isData  _  _                   = False

isVar   f (Var   _ id _ _)     = f id
isVar   _  _                   = False

isFunc  f (Func  _ id _ _)     = f id
isFunc  _  _                   = False

isAny f s = isClass f s || isData f s || isVar  f s || isFunc f s

true x = True

-------------------------------------------------------------------------------

errDeclared :: Ann -> String -> String -> [Stmt] -> Errors
errDeclared z str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing  -> []
            (Just _) -> [toError z str ++ " '" ++ id ++ "' is already declared"]

getErrsTypesDeclared :: Ann -> Type -> [Stmt] -> Errors
getErrsTypesDeclared z tp ids = concatMap aux $ map (\id->(id, find (isData $ (==)id) ids)) $ Type.get1s tp
    where
        aux (id, Nothing) = [toError z "type '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

-------------------------------------------------------------------------------

call :: Ann -> [Stmt] -> ID_Func -> Exp -> (Errors, Type, Exp, String)
call z ids id exp = (es++es_exp, tp_out, exp', fid)
  where
    (es_exp, exp') = expr ids exp
    tp_exp' = type_ $ getAnn exp'

    -- find in top-level funcs | f : A -> B
    (fid,tp_out,es) =
      case find (isFunc $ (==)id) ids of
        -- found in top-level `Func`
        (Just (Func _ _ (TypeF inp out) _)) ->
          case inp `supOf` tp_exp' of
            Left  es         -> ("???", out,                         map (toError z) es)
            Right (tp,insts) -> (id,    Type.instantiate insts out, [])

        -- find in classes | class X a with ...
        Nothing ->
          case find (\(_,f)->isJust f) $ map cls2func $ filter (isClass true) ids of
            -- not found
            Nothing -> ("???", TypeB, [toError z "function '" ++ id ++ "' is not declared"])

            -- found in class | class X a with f : C -> a -> b
            -- find instance matching call | f x y:A z
            --    instantiate 'a' in 'f' using call to find 'A'
            -- find 'X A' with 'f : C -> A -> b'
            Just (Class _ id' [var] _ _, Just (Func _ id (TypeF inp out) _)) ->
              case inp `supOf` tp_exp' of
                Left  es         -> ("???", out,                      map (toError z) es)
                Right (_,insts) ->
                  let tp = Type.instantiate insts (TypeV var) in
                    case find (isSubOf tp . getTP) $ filter (isInst $ (==id')) (sort' ids) of
                      Nothing -> ("???",
                                  out,
                                  [toError z "call for '" ++ id ++ "' has no instance in '" ++ id' ++ "'"])
                      Just (Inst _ _ [tp'] _ _) ->
                                 (Type.show' tp' ++ "__" ++ id,
                                  Type.instantiate insts out,
                                  [])

    cls2func cls = (cls, find (isFunc $ (==)id) (classinst2ids cls))
    getTP (Inst _ _ [tp] _ _) = tp
    sort' ids = ids -- TODO: sort by subtyping (topological order)

classinst2ids :: Stmt -> [Stmt]
classinst2ids p = case p of
    (Class _ _ _ ifc _) -> aux ifc
    (Inst  _ _ _ imp _) -> aux imp
    where
        aux (Nop _)          = []
        aux s@(Func _ _ _ p) = s : aux p

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
        (es2,imp') = stmt (filter (not . (isClass $ (==)id)) ids) imp -- prevent clashes w/ own class
        (es3,p')   = stmt (s:ids) p

        -- check if this instance is already declared
        es1 = case find isSameInst ids of
            Nothing  -> []
            (Just _) -> [toError z "instance '" ++ id ++ " (" ++
                         intercalate "," [Type.show' tp] ++ ")' is already declared"]
        isSameInst (Inst _ id' [tp'] _ _) = (id==id' && [tp]==[tp'])
        isSameInst _                     = False

        -- check if class exists
        -- compares class vs instance function by function in order
        es0 = case find (isClass $ (==)id) ids of
            Nothing                      -> [toError z "typeclass '" ++ id ++ "' is not declared"]
            Just (Class _ _ [var] ifc _) -> compares ifc imp where
                compares (Func _ id1 tp1 p1) (Func  _ id2 tp2   p2) =
                    (names id1 id2) ++ (instOf var tp1 tp2) ++ (compares p1 p2)
                compares (Nop _) (Nop _) = []

        -- check if function names are the same
        names id1 id2 | id1==id2  = []
                      | otherwise = [toError z "names do not match : expected '" ++ id1 ++ "' : found '" ++ id2 ++ "'"]

        -- check if (Inst tps) match (Class vars) in all functions
        instOf var tp1 tp2 = case tp1 `supOf` tp2 of
                              Left es -> es
                              Right (_,insts) ->
                                let tp' = Type.instantiate insts (TypeV var) in
                                  if tp' == tp then []
                                               else ["types do not match : expected '" ++
                                                    (Type.show' tp) ++ "' : found '" ++
                                                    (Type.show' tp') ++ "'"]

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
    (es, (es',p')) = case find (isFunc $ (==)id) ids of
        Nothing               -> ([],                                   stmt (s:ids) p)
        Just (Func _ _ tp' _) -> (map (toError z) (supOfErrors tp' tp), stmt ids p)
    es_data = getErrsTypesDeclared z tp ids

    -- check if clashes with functions in classes
    es_dcl = errDeclared z "function" id ids'
    ids' = concatMap classinst2ids $ filter (isClass true) ids

stmt ids s@(FuncI z id tp imp p) = (es1++es2, FuncI z id tp imp' p')
                                   where
                                    (es1,imp') = stmt ids imp
                                    (es2,p')   = stmt ids p

stmt ids (Write z loc exp)   = (es1 ++ es2 ++ es3, Write z loc exp')
                               where
                                (tps_loc, es1) = aux loc
                                aux :: Loc -> (Type, Errors)
                                aux LAny       = (TypeT, [])
                                aux (LVar var) = case find (isVar $ (==)var) ids of
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
                                es3        = map (toError z) (supOfErrors tps_loc (type_ $ getAnn exp'))

stmt ids (CallS z id exp)   = (es, SCallS z id' exp') where
                              (es,_,exp',id') = call z ids id exp

stmt ids (If  z exp p1 p2)   = (ese ++ es ++ es1 ++ es2, If z exp' p1' p2')
                               where
                                (ese,exp') = expr ids exp
                                es = map (toError z) (supOfErrors (Type1 "Bool") (type_ $ getAnn exp'))
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq z p1 p2)       = (es1++es2, Seq z p1' p2')
                               where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)          = (es, Loop z p')
                               where
                                (es,p') = stmt ids p

stmt ids (Ret z exp)         = (es, Ret z exp')
                               where
                                (es,exp') = expr ids exp

stmt _   (Nop z)             = ([], Nop z)

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> (Errors, Exp)

expr _   (Number z val)  = ([], Number z{type_=Type1 "Int"} val)
expr _   (Unit z)        = ([], Unit   z{type_=Type0})

expr ids (Cons  z id)    = (es, Cons  z{type_=(Type1 id)} id)
    where
        es = case find (isData $ (==)id) ids of
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
                            (tp',es) = case find (isVar $ (==)id) ids of
                                        Nothing               -> (TypeB, [toError z "variable '" ++ id ++ "' is not declared"])
                                        (Just (Var _ _ tp _)) -> (tp,    [])

expr ids (Call z id exp) = (es, SCall z{type_=tp_out} id' exp') where
                           (es, tp_out, exp', id') = call z ids id exp
