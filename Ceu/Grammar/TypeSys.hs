module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate, unfoldr)
import Data.Maybe (isJust, fromJust)
import Data.Bool (bool)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type as Type (Type(..), show', supOf, isSubOf, supOfErrors, instantiate, get1s, getSuper, cat)
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic

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

isAny f s = isClass f s || isData f s || isVar  f s

classinst2ids :: Stmt -> [Stmt]
classinst2ids p = case p of
    (Class _ _ _ ifc _) -> aux ifc
    (Inst  _ _ _ imp _) -> aux imp
    where
        --aux (Nop _)                   = []
        aux s@(Var _ _ _ p)           = [s] -- : aux p
        aux (Seq _ s@(Var _ _ _ p) _) = s : aux p

-------------------------------------------------------------------------------

errDeclared :: Ann -> String -> String -> [Stmt] -> Errors
errDeclared z str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing  -> []
            (Just _) -> [toError z str ++ " '" ++ id ++ "' is already declared"]

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap aux $ map (\id->(id, find (isData $ (==)id) ids)) $ Type.get1s tp
    where
        aux (id, Nothing) = [toError z "type '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

-------------------------------------------------------------------------------

call :: Ann -> Type -> [Stmt] -> Exp -> Exp -> (Errors, Type, Exp, Exp)
call z tp_xp ids f exp = (bool es_exp es_f (null es_exp), out, f', exp')
  where
    (es_f,   f')   = expr z (TypeF (type_$getAnn$exp') tp_xp) ids f
    (es_exp, exp') = expr z inp ids exp
    (inp,out) = case type_ $ getAnn f' of
      TypeF inp' out' -> (inp',out')
      otherwise       -> (TypeV "?", TypeV "?")
    --xx = traceShow $ [tp_xp,(type_$getAnn$exp')]

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
        isSameInst _                      = False

        -- check if class exists
        -- compares class vs instance function by function in order
        es0 = case find (isClass $ (==)id) ids of
            Nothing                      -> [toError z "typeclass '" ++ id ++ "' is not declared"]
            Just (Class _ _ [var] ifc _) -> compares ifc imp where
                compares (Var _ id1 tp1 (Nop _))
                         (Var _ id2 tp2 _)            = (names id1 id2) ++
                                                        (instOf var tp1 tp2)
                compares (Var _ id1 tp1 (Seq _ _ p1))
                         (Var _ id2 tp2 (Seq _ _ p2)) = (names id1 id2) ++
                                                        (instOf var tp1 tp2) ++
                                                        (compares p1 p2)
                compares x y = error $ show [x,y]
                --compares (Nop _) (Nop _) = []

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

stmt ids s@(Data z id [] flds abs p) = (es_dcl ++ (errDeclared z "type" id ids) ++ es,
                                        s')
  where
    s'             = Data z id [] flds' abs p'
    (es,p')        = stmt (s':ids) p
    (flds',es_dcl) =
      case Type.getSuper (Type1 id) of
        Nothing          -> (flds, [])
        Just (Type1 sup) -> (Type.cat sups flds,
                             (getErrsTypesDeclared z ids (Type1 sup)) ++
                             (getErrsTypesDeclared z ids flds))
                            where
                              sups = case find (isData $ (==)sup) ids of
                                      Nothing                     -> Type0
                                      Just (Data _ _ _ sups' _ _) -> sups'

stmt ids s@(Data z id vars flds abs p) = error "not implemented"

stmt ids s@(Var  z id tp p) = (es_data ++ es_dcl ++ es_id ++ es, Var z id tp p')
                              where
                                es_data = getErrsTypesDeclared z ids tp
                                es_id   = errDeclared z "variable" id ids
                                (es,p') = stmt (s:ids) p
                                es_dcl = errDeclared z "variable" id ids'
                                ids' = concatMap classinst2ids $ filter (isClass $ const True) ids

stmt ids (Write z loc exp) = (es1 ++ es2, Write z loc exp')
                             where
                              (tps_loc, es1) = aux loc
                              aux :: Loc -> (Type, Errors)
                              aux LAny       = (TypeT, [])
                              aux (LVar var) = case find (isVar $ (==)var) ids of
                                                Nothing ->
                                                  (TypeT, [toError z "variable '" ++ var ++ "' is not declared"])
                                                Just (Var _ _ tp _) ->
                                                  (tp,    [])
                              aux LUnit      = (Type0, [])
                              aux (LNumber v)= (Type1 "Int", [])
                              aux (LTuple l) = (TypeN tps, es) where
                                                l' :: [(Type,Errors)]
                                                l' = map aux l
                                                (tps,es) = foldr cat ([],[]) l'
                                                cat (tp,es1) (tps,es2) = (tp:tps, es1++es2)

                              (es2,exp') = expr z tps_loc ids exp
                                -- VAR: I expect exp.type to be a subtype of tps_loc

stmt ids (CallS z f exp)   = (es, CallS z f' exp')
                             where
                              (es, _, f', exp') = call z (TypeV "?") ids f exp

-------------------------------------------------------------------------------


stmt ids (If z exp p1 p2)   = (ese ++ es1 ++ es2, If z exp' p1' p2')
                              where
                                (ese,exp') = expr z (Type1 "Bool") ids exp
                                  -- VAR: I expect exp.type to be a subtype of Bool
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Seq z p1 p2)      = (es1++es2, Seq z p1' p2')
                              where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)         = (es, Loop z p')
                              where
                                (es,p') = stmt ids p

stmt ids (Ret z exp)        = (es, Ret z exp')
                              where
                                (es,exp') = expr z TypeT ids exp
                                  -- VAR: I expect exp.type to be a subtype of Top (any type)

stmt _   (Nop z)            = ([], Nop z)

-------------------------------------------------------------------------------

expr :: Ann -> Type -> [Stmt] -> Exp -> (Errors, Exp)
expr z tp_xp ids exp = (es1++es2, exp') where
  (es1, exp') = expr' tp_xp ids exp
  es2 = if not.null $ es1 then [] else
          map (toError z) (tp_xp `supOfErrors` (type_ $ getAnn exp'))

-- TODO: use tp_xp in the cases below:
--  * number: decide for float/int/etc
--  * cons:   ?
--  * tuple:  instantiate sub exps

expr' :: Type -> [Stmt] -> Exp -> (Errors, Exp)

expr' _ _   (Number z val)   = ([], Number z{type_=Type1 "Int"} val)
expr' _ _   (Unit   z)       = ([], Unit   z{type_=Type0})
expr' _ _   (Arg    z)       = ([], Arg    z{type_=TypeB})
expr' _ ids (Func   z tp p)  = (es, Func   z{type_=tp} tp p')
                               where
                                (es,p') = stmt ids p

expr' _ ids (Cons  z id exp) = (es++es_exp, Cons z{type_=(Type1 id)} id exp')
    where
        (tp,es) = case find (isData $ (==)id) ids of
            Nothing                      ->
              (TypeV "?", [toError z "type '" ++ id ++ "' is not declared"])
            Just (Data _ _ _ tp True  _) ->
              (tp,        [toError z "type '" ++ id ++ "' is abstract"])
            Just (Data _ _ _ tp False _) ->
              (tp,        [])
        (es_exp, exp') = expr z tp ids exp

expr' _ ids (Tuple z exps)   = (es, Tuple z{type_=tps'} exps')
                               where
                                rets :: [(Errors,Exp)]
                                rets  = map (\e -> expr z TypeT ids e) exps
                                es    = concat $ map fst rets
                                exps' = map snd rets
                                tps'  = TypeN (map (type_.getAnn) exps')

expr' tp_xp ids (Read z id)  = if id == "_INPUT" then
                                ([], Read z{type_=Type1 "Int"} id)
                               else
                                (es, Read z{type_=tp_ret} id)
  where
    -- find in top-level ids | id : a
    (tp_ret,es) =
      case find (isVar $ (==)id) ids of
        Just (Var _ _ tp _) -> (tp, [])   -- found
        Nothing             ->            -- not found
          -- find in classes | class X a with id : a
          case find (\(_,var) -> isJust var)            -- Just (clsI, Just (Var ...))
               $ map (\(cls,ids) -> (cls, find (isVar $ (==)id) ids)) -- [(cls1,Just (Var .)), .]
               $ map (\cls -> (cls, classinst2ids cls)) -- [(cls1,ids1), ...]
               $ filter (isClass $ const True) ids              -- [cls1,cls2, ...]
            of
            -- not found
            Nothing -> (TypeV "?", [toError z "variable '" ++ id ++ "' is not declared"])

            -- find matching instance | id : a=<tp_xp>
            Just (Class _ cls [var] _ _, Just (Var _ id tp_var _)) ->
              case tp_xp `supOf` tp_var of
                Left  es        -> (TypeV "?", map (toError z) es)
                Right (_,insts) ->
                  let tp = Type.instantiate insts (TypeV var) in
                    case find (isSubOf tp . getTP) $ filter (isInst $ (==cls)) (sort' ids) of
                      Nothing   -> (TypeV "?",
                                    [toError z "variable '" ++ id ++
                                     "' has no associated instance for type '" ++
                                     Type.show' tp_xp ++ "' in class '" ++ cls ++ "'"])
                      Just inst -> (getTP $ fromJust
                                          $ find (isVar $ (==)id) (classinst2ids inst),
                                    [])

    getTP (Inst _ _ [tp] _ _) = tp
    getTP (Var  _ _ tp _)     = tp
    sort' ids = ids -- TODO: sort by subtyping (topological order)

expr' xp ids (Call z f exp) = (es, Call z{type_=out} f' exp')
                                 where
                                  (es, out, f', exp') = call z xp ids f exp
