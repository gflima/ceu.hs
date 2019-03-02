module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate, unfoldr, unzip4, sortBy)
import Data.Maybe (isJust, fromJust)
import Data.Bool (bool)

import Ceu.Grammar.Globals
import Ceu.Grammar.Type as Type (Type(..), show', instantiate, get1s, getSuper,
                                 cat, hier2str,
                                 Relation(..), relates, isRel, relatesErrors)
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic

fromLeft (Left v) = v

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p
--go p = traceShowId $ stmt [] p

-------------------------------------------------------------------------------

isClass f (Class _ (id,_) _ _ _) = f id
isClass _  _                     = False

isInst  f (Inst  _ (id,_) _ _)   = f id
isInst  _  _                     = False

isData  f (Data  _ hr _ _ _ _)   = f (Type.hier2str hr)
isData  _  _                     = False

isVar   f (Var   _ id _ _)       = f id
isVar   _  _                     = False

isAny :: (String -> Bool) -> Stmt -> Bool
isAny f s = isClass f s || isData f s || isVar  f s

clssinst2ids :: Stmt -> [(Stmt,Bool)]
clssinst2ids p = sortBy fsort $
  case p of
    (Class _ _ _ ifc _) -> aux ifc
    (Inst  _ _ imp _)   -> aux imp
  where
    aux :: Stmt -> [(Stmt,Bool)]
    aux s@(Var _ _ _ (Match _ _ _ _ p _)) = (s,True)  : aux p
    aux s@(Var _ _ _ p)                   = (s,False) : aux p
    aux (Nop _)                           = []
    --aux p = error $ show p

    fsort :: (Stmt,Bool) -> (Stmt,Bool) -> Ordering
    fsort (Var _ a _ _,_) (Var _ b _ _,_) = compare a b

err z = Ret z $ Error z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> String -> String -> [Stmt] -> Errors
errDeclared z str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing  -> []
            (Just _) -> [toError z $ str ++ " '" ++ id ++ "' is already declared"]

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap aux $ map (\id->(id, find (isData $ (==)id) ids)) $ Type.get1s tp
    where
        aux (id, Nothing) = [toError z $ "type '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids (Class z (id,[var]) exts ifc p) = (es0 ++ es1 ++ es2 ++ es3, ret) where
    es0 = errDeclared z "interface" id ids
    (es3,p')   = stmt (s':ids) p
    (es2,ifc') = stmt ids ifc
    s'         = Class z (id,[var]) exts ifc' (Nop z)

    es1 = concatMap f exts
    f (sup,_) = case find (isClass $ (==)sup) ids of
      Nothing -> [toError z $ "interface '" ++ sup ++ "' is not declared"]
      Just _  -> []

    ret = foldr f p' ids' where
      ids' = map fst $ clssinst2ids s'

      -- Method w implementation (=/=)
      f (Var z1 id1 tp1 (Match z2 False l2 exp2 t2  f2)) acc =
        (Var z1 id1 tp1 (Match z2 False l2 exp  acc f2))
        where
          Func z tp p = exp2
          exp = Func z tp $ vtable z p

          -- add vtable to scope
          --  ((===, =/=), ...) <- _vtable
          vtable z p = Match z False
                        (LTuple (map (\(Var _ id _ _)-> LVar id) ids'))
                        (Read z "_vtable")
                        p (err z)

      -- Method w/o implementation (===)
      f (Var z1 id1 tp1 _) acc = Var z1 id1 tp1 acc

stmt ids (Class _ (id,vars) _ _ _) = error "not implemented: multiple vars"

stmt ids (Inst z (id,[inst_tp]) imp p) =
  let (esp,p')   = stmt (s':ids) p
      (esi,imp') = stmt (filter (not . (isClass $ (==)id)) ids) imp
                         -- prevent clashes w/ own class
      s'         = Inst z (id,[inst_tp]) imp' (Nop z)
  in
    -- check if class is declared
    case find (isClass $ (==)id) ids of

      Nothing -> (es++esi++esp, p') where
                 es = [toError z $ "interface '" ++ id ++ "' is not declared"]

      Just cls@(Class _ (_,[clss_var]) exts ifc _) ->

        -- check if this instance is already declared
        case find isSameInst ids of
          Just _  -> (es++esi++esp, p') where
                     es = [toError z $ "instance '" ++ id ++ " (" ++
                           intercalate "," [Type.show' inst_tp] ++ ")' is already declared"]

          -----------------------------------------------------------------------
          -- class is declared and instance does not exist
          -----------------------------------------------------------------------

          Nothing -> (es1++es2++esi++esp, ret) where

            -- check extends
            --  interface      (Eq  for a)
            --  implementation (Eq  for Bool)                  <-- so Bool must implement Eq
            --  interface      (Ord for a) extends (Eq for a)  <-- but Ord extends Eq
            --  implementation (Ord for Bool)                  <-- Bool implements Ord
            es1 = concatMap f exts where
              f (sup,_) = case find (isInstOf (sup,[inst_tp])) ids of
                Nothing -> [toError z $ "implementation '" ++ sup ++ " for " ++
                            (Type.show' inst_tp) ++ "' is not declared"]
                Just _  -> []
              isInstOf me (Inst _ me' _ _) = (me == me')
              isInstOf _  _                = False

            ---------------------------------------------------------------------

            -- compares class vs instance function by function (sorted)
            -- also collects implementations to add wrappers to Inst
            (es2,imps) = compares (clssinst2ids cls) (clssinst2ids s') where
              --compares :: [a] -> [a] -> (Errors, [Maybe (Bool,Stmt)])
              compares [] [] = ([], [])

              compares ((imp@(Var z1 id1 tp1 _), has1):l1) [] =
                (bool ([toError z $ "missing implementation of '" ++ id1 ++ "'"], [Nothing])
                      ([], [Just (True,imp)]) -- class impl
                      has1)
                  +++ compares l1 []

              compares [] ((Var z2 id2 _ _, _):l2) =
                ([toError z2 $ "unexpected implementation of '" ++ id2 ++ "'"],[])
                  +++ compares [] l2

              compares ((imp1@(Var z1 id1 tp1 _), has1):l1)
                       l2'@((imp2@(Var z2 id2 tp2 imp), has2):l2) =
                if id1 == id2 then
                  let es = case imp of
                            Match _ _ _ _ _ _ -> []
                            otherwise -> [toError z2 $ "missing implementation of '" ++ id2 ++ "'"]
                  in
                    (clssVSinst z2 tp1 tp2 ++ es, [Just (False,imp2)]) +++ compares l1 l2
                else                          -- inst impl
                  if has1 then
                    ([],[Just (True,imp1)]) +++ compares l1 l2'
                  else                        -- class impl
                    ([toError z $ "missing implementation of '" ++ id1 ++ "'"],[Nothing])
                      +++ compares l1 l2'

              compares _ ((y,_):_) = ([toError (getAnn y) $ "unexpected statement"], [])

              -- check if (Inst tps) match (Class vars) in all functions
              clssVSinst z tp1 tp2 =
                case relates SUP tp1 tp2 of
                  Left es -> map (toError z) es
                  Right (_,insts) ->
                    let tp' = Type.instantiate insts (TypeV clss_var) in
                      if tp' == inst_tp then []
                                   else [toError z $ "types do not match : expected '" ++
                                        (Type.show' inst_tp) ++ "' : found '" ++
                                        (Type.show' tp') ++ "'"]
              (+++) (a1,b1) (a2,b2) = (a1++a2, b1++b2)

            ---------------------------------------------------------------------

            (esp,p') = stmt (vars' (Nop z) : s' : ids) p

            ret = vars' $ --traceShowId $
                    if all isJust imps then
                      -- _inst__Eq__tp <- (===, =/=)
                      -- (===__tp, =/=__tp) <- _inst__Eq__tp
                      Match z False (LVar id') (Tuple z $ map f1 imps)
                        (Match z False (LTuple $ map f2 imps) (Read z id')
                          p'
                          (err z))
                        (err z)
                    else
                      p'
                    where
                      -- inst impl
                      f1 (Just (False, Var _ _ _ (Match _ _ _ exp _ _))) = exp
                      f1 (Just (False, Var _ _ _ _)) = Error z (-2) -- TODO: to pass tests

                      -- class impl (=/=)
                      --  func (...) _vtable=inst ; return call (=/=) (...)
                      f1 (Just (True,  Var _ id tp _)) = exp
                         where
                          exp = Func z tp
                                  (Match z False (LVar "_vtable") (Read z id')
                                    (Ret z $ Call z (Read z id) (Read z "_arg"))
                                    (err z))

                      f1 p = error $ show p

                      f2 (Just (_, Var _ id tp _)) = --traceShowId $
                        LVar $ id ++ "__" ++
                          Type.show' (Type.instantiate [(clss_var,inst_tp)] tp)

            vars' p = Var z id'
                      (TypeN $ map (\(Var _ _ tp _)->tp) $ map fst $ clssinst2ids s')
                      (foldr f3 p imps) where
                        f3 (Just (_, Var z id tp _)) p =
                          Var z (id ++ "__" ++ Type.show' tp') tp' p where
                            tp' = Type.instantiate [(clss_var,inst_tp)] tp

            id' = intercalate "__" ["_inst",id,Type.show' inst_tp]

          -----------------------------------------------------------------------

        where
          isSameInst (Inst _ (id',[tp']) _ _) = (id==id' && [inst_tp]==[tp'])
          isSameInst _                        = False

stmt ids (Inst _ (_,tps) _ _) = error "not implemented: multiple types"

stmt ids s@(Data z hr [] flds abs p) = (es_dcl ++ (errDeclared z "type" (Type.hier2str hr) ids) ++ es,
                                        s')
  where
    s'             = Data z hr [] flds' abs p'
    (es,p')        = stmt (s':ids) p
    (flds',es_dcl) =
      case Type.getSuper (Type1 hr) of
        Nothing          -> (flds, [])
        Just (Type1 sup) -> (Type.cat sups flds,
                             (getErrsTypesDeclared z ids (Type1 sup)) ++
                             (getErrsTypesDeclared z ids flds))
                            where
                              sups = case find (isData $ (==)(Type.hier2str sup)) ids of
                                      Nothing                     -> Type0
                                      Just (Data _ _ _ sups' _ _) -> sups'

stmt ids s@(Data z hr vars flds abs p) = error "not implemented"

stmt ids s@(Var  z id tp p) = (es_data ++ es_dcl ++ es_id ++ es, Var z id tp p')
                              where
                                es_data = getErrsTypesDeclared z ids tp
                                es_id   = errDeclared z "variable" id ids
                                (es,p') = stmt (s:ids) p
                                es_dcl = errDeclared z "variable" id ids'
                                ids' = map fst $ concatMap clssinst2ids $ filter (isClass $ const True) ids

stmt ids (Match z chk loc exp p1 p2) = (esc++esa++es1++es2, Match z chk loc' (fromJust mexp) p1' p2')
  where
    (es1, p1') = stmt ids p1
    (es2, p2') = stmt ids p2
    (chk', esa, loc', mexp) = aux ids z loc (Right exp)

    -- set  x <- 1    // chk=false
    -- set! 1 <- x    // chk=true
    -- if   1 <- x    // chk=true
    esc = if null esa then
            if chk then
              bool [toError z "match never fails"] [] chk'
            else
              bool [toError z "match might fail"]  [] (not chk')
          else
            []

    f :: (Relation,Type) -> Either Type Exp -> (Errors, Maybe Exp)
    f (rel,txp) tpexp =
      case tpexp of
        Left  tp  -> (map (toError z) (relatesErrors rel txp tp), Nothing)
        Right exp -> (es, Just exp') where (es,exp') = expr z (rel,txp) ids exp

    fchk :: Type -> Maybe Exp -> Either Type Exp -> Bool
    fchk txp mexp tpexp = not $ isRel SUP txp (maybe (fromLeft tpexp) (type_.getAnn) mexp)

    -- Match must be covariant on variables and contravariant on constants:
    --  LVar    a     <- x      # assign # a     SUP x
    --  LExp    a     <- x      # match  # a     SUP x
    --  LAny          <- x      # match  # BOT   SUB x
    --  LUnit         <- x      # match  # unit  SUB x
    --  LNumber a     <- x      # match  # Int.X SUB x
    --  LCons   a b   <- Cons x # match  # a     SUP Cons x | b match x
    --  LCons   a b   <- x      # match  # a     ANY x      | b match x
    --  LTuple  (a,b) <- (x,y)  # match  # (B,B) SUB (x,y)  | a match x,  b match y
    --  LTuple  (a,b) <- x      # match  # (B,B) SUB x      | a match x1, b match x2

    aux :: [Stmt] -> Ann -> Loc -> Either Type Exp -> (Bool, Errors, Loc, Maybe Exp)
    aux ids z loc tpexp =
      case loc of
        LAny         -> (False, ese, loc, mexp) where (ese,mexp) = f (SUB,TypeB) tpexp
        LUnit        -> (chk',  ese, loc, mexp) where (ese,mexp) = f (SUB,txp)   tpexp
                                                      txp  = Type0
                                                      chk' = fchk txp mexp tpexp
        (LNumber v)  -> (chk',  ese, loc, mexp) where (ese,mexp) = f (SUB,txp)   tpexp
                                                      txp  = Type1 ["Int",show v]
                                                      chk' = fchk txp mexp tpexp
        (LVar var)   -> (False, esl++ese, loc, mexp)
          where
            (tpl,esl)  = case find (isVar $ (==)var) ids of
              (Just (Var _ _ tp _)) -> (tp,    [])
              Nothing               -> (TypeT, [toError z $ "variable '" ++ var ++ "' is not declared"])
            (ese,mexp) = f (SUP,tpl) tpexp
        (LExp e)     -> (True, es++ese, LExp e', mexp)
          where
            (ese,mexp) = f (SUP, type_ $ getAnn e') tpexp
            (es, e')   = expr z (SUP,TypeT) ids e

        (LCons hr l) -> (fchk txp mexp tpexp || chk1, esd++esl++es'++ese, LCons hr l', mexp)
          where
            txp       = Type1 hr
            str       = Type.hier2str hr
            (tpd,esd) = case find (isData $ (==)str) ids of
              Just (Data _ _ _ tp _ _) -> (tp,    [])
              Nothing                  -> (TypeT, [toError z $ "type '" ++ str ++ "' is not declared"])

            (ese,mexp)      = f (rel,txp) tpexp
            (chk2,esl,l',_) = aux ids z l (Left tpd)

            -- if any errors found, ignore all this
            (rel,chk1,es') = case tpexp of
              Right (Cons _ _ e) -> (SUP,chk,es) where
                (chk,es) = if null esl && null ese then
                            let (chk',es',_,_) = aux ids z l (Right e) in (chk',es')
                           else
                            (chk2,[]) -- use chk2 -> chk1
              otherwise          -> (ANY,chk2,[])

        (LTuple ls)  -> (or chks, concat esls ++ ese, LTuple ls', toexp mexps'')
          where
            (ese,mexp) = f (SUB,TypeN $ map (const$TypeV "?") ls) tpexp
            (chks, esls, ls'', mexps'') = unzip4 $ zipWith (aux ids z) ls' mexps'
            (ls', mexps', toexp) = case tpexp of
              Right exp ->
                case exp of
                  -- (a,b,c) <- (x,y,z)
                  (Tuple z' exps) -> (ls', exps', toexp) where
                    toexp :: [Maybe Exp] -> Maybe Exp
                    toexp exps = Just $ Tuple z'{type_=TypeN (map (type_.getAnn) exps')} exps'
                                 where
                                  exps' = map fromJust exps
                    exps' = map Right exps ++
                            replicate (length ls - length exps) (Left $ TypeV "?")
                    ls'   = ls ++ replicate (length exps - length ls) LAny

                  -- (a,b,c) <- x
                  otherwise -> (ls', tps', \_->mexp) where
                    tps' = map Left tps ++
                           replicate (length ls - length tps) (Left $ TypeV "?")
                    ls'  = ls ++ replicate (length tps - length ls) LAny
                    tps  = case type_ $ getAnn $ fromJust mexp of
                      (TypeN x) -> x
                      x         -> [x]

              -- (k, (a,b,c)) <- x
              Left tp -> (ls', tps', \_->Nothing) where
                tps' = map Left tps ++
                       replicate (length ls - length tps) (Left $ TypeV "?")
                ls'  = ls ++ replicate (length tps - length ls) LAny
                tps  = case fromLeft tpexp of
                  (TypeN x) -> x
                  x         -> [x]

stmt ids (CallS z exp) = (ese++esf, CallS z exp') where
                         (ese, exp') = expr z (SUP,TypeV "?") ids exp
                         esf = case exp' of
                          Call _ _ _ -> []
                          otherwise  -> [toError z "expected call"]

-------------------------------------------------------------------------------


{-
stmt ids (If z exp p1 p2)   = (ese ++ es1 ++ es2, If z exp' p1' p2')
                              where
                                (ese,exp') = expr z (Type1 ["Bool"]) ids exp
                                  -- VAR: I expect exp.type to be a subtype of Bool
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
-}

stmt ids (Seq z p1 p2)      = (es1++es2, Seq z p1' p2')
                              where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)         = (es, Loop z p')
                              where
                                (es,p') = stmt ids p

stmt ids (Ret z exp)        = (es, Ret z exp')
                              where
                                (es,exp') = expr z (SUP,TypeT) ids exp
                                  -- VAR: I expect exp.type to be a subtype of Top (any type)

stmt _   (Nop z)            = ([], Nop z)

-------------------------------------------------------------------------------

expr :: Ann -> (Relation,Type) -> [Stmt] -> Exp -> (Errors, Exp)
expr z (rel,txp) ids exp = (es1++es2, exp') where
  (es1, exp') = expr' (rel,bool (TypeV "?") txp (rel==SUP)) ids exp
                           -- only force expected type on SUP
  es2 = if not.null $ es1 then [] else
          map (toError z) (relatesErrors rel txp (type_ $ getAnn exp'))

  -- https://en.wikipedia.org/wiki/Subtyping
  -- If S is a subtype of T, the subtyping relation is often written S <: T,
  -- to mean that any term of type S can be safely used in a context where a
  -- term of type T is expected.
  --    txp = T :> S = exp'.type

-- TODO: use txp in the cases below:
--  * number: decide for float/int/etc
--  * cons:   ?
--  * tuple:  instantiate sub exps

expr' :: (Relation,Type) -> [Stmt] -> Exp -> (Errors, Exp)

expr' _       _   (Error  z v)     = ([], Error  z{type_=TypeB} v)
expr' _       _   (Number z v)     = ([], Number z{type_=Type1 ["Int",show v]} v)
expr' _       _   (Unit   z)       = ([], Unit   z{type_=Type0})
expr' (_,txp) _   (Arg    z)       = ([], Arg    z{type_=txp})
expr' _       ids (Func   z tp p)  = (es, Func   z{type_=tp} tp p')
                                     where
                                      (es,p') = stmt ids p

expr' _ ids (Cons  z hr exp) = (es++es_exp, Cons z{type_=(Type1 hr)} hr exp')
    where
        hr_str = Type.hier2str hr
        (tp,es) = case find (isData $ (==)hr_str) ids of
            Nothing                      ->
              (TypeV "?", [toError z $ "type '" ++ hr_str ++ "' is not declared"])
            Just (Data _ _ _ tp True  _) ->
              (tp,        [toError z $ "type '" ++ hr_str ++ "' is abstract"])
            Just (Data _ _ _ tp False _) ->
              (tp,        [])
        (es_exp, exp') = expr z (SUP,tp) ids exp

expr' _ ids (Tuple z exps) = (es, Tuple z{type_=tps'} exps') where
                              rets :: [(Errors,Exp)]
                              rets  = map (\e -> expr z (SUP,TypeV "?") ids e) exps
                              es    = concat $ map fst rets
                              exps' = map snd rets
                              tps'  = TypeN (map (type_.getAnn) exps')

expr' (rel,txp) ids (Read z id) = (es, Read z{type_=tp} id') where
  (id', tp, es) =
    if id == "_INPUT" then
      (id, Type1 ["Int"], [])
    else
      -- find in top-level ids | id : a
      case find (isVar $ (==)id) ids of
        Just (Var _ _ tp _) -> (id, tp, [])   -- found
        Nothing             ->                -- not found
          -- find in classes | class X a with id : a
          case find (\(_,var) -> isJust var)            -- Just (clsI, Just (Var ...))
               $ map (\(cls,ids) -> (cls, find (isVar $ (==)id) ids)) -- [(cls1,Just (Var .)), .]
               $ map (\cls -> (cls, map fst $ clssinst2ids cls)) -- [(cls1,ids1), ...]
               $ filter (isClass $ const True) ids              -- [cls1,cls2, ...]
            of
            -- not found
            Nothing -> (id, TypeV "?", [toError z $ "variable '" ++ id ++ "' is not declared"])

            -- find matching instance | id : a=<txp>
            Just pp@(Class _ (cls,[clss_var]) _ _ _, Just (Var _ id tp_var _)) ->
              case relates rel txp tp_var of
                Left  es        -> (id, TypeV "?", map (toError z) es)
                Right (_,insts) ->
                  let tp = Type.instantiate insts (TypeV clss_var) in
                    case find (isRel SUB tp . getTP) $ filter (isInst $ (==cls)) (sort' ids) of
                      Nothing -> (id, TypeV "?",
                                  [toError z $ "variable '" ++ id ++
                                   "' has no associated instance for type '" ++
                                   Type.show' txp ++ "' in class '" ++ cls ++ "'"])
                      Just (Inst _ (_,[inst_tp]) _ _) ->
                        (id ++ "__" ++ Type.show' tp', tp', []) where
                          tp' = Type.instantiate [(clss_var,inst_tp)] $ getTP $
                                  fromJust $ find (isVar $ (==)id)
                                                  (map fst $ clssinst2ids (fst pp))
                        --case find (isVar $ (==)id) (map fst $ clssinst2ids inst) of
                          --Just p  -> (getTP p, [])
                          --Nothing -> (getTP $ fromJust $ find (isVar $ (==)id) (map fst $ clssinst2ids (fst pp)), [])
              where
                getTP (Inst _ (_,[tp]) _ _) = tp
                getTP (Var  _ _ tp _)       = tp
                sort' ids = ids -- TODO: sort by subtyping (topological order)

expr' (rel,txp) ids (Call z f exp) = (bool es_exp es_f (null es_exp),
                                     Call z{type_=tp_out} f' exp')
  where
    (es_exp, exp') = expr z (rel,TypeV "?") ids exp
    (es_f,   f')   = expr z (rel,TypeF (type_$getAnn$exp') txp) ids f

    tp_out = case type_ $ getAnn f' of
      TypeF _ out -> out
      otherwise   -> txp
