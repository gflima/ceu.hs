module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate, unfoldr, unzip4, sortBy)
import Data.Maybe (isJust, fromJust)
import Data.Bool (bool)
import qualified Data.Map as Table

import Ceu.Grammar.Globals
import Ceu.Grammar.Type as Type (Type(..), show', instantiate, getDs, getVs, getSuper,
                                 cat, hier2str, isParametric,
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

clssinst2table :: Stmt -> Table.Map ID_Var Stmt
clssinst2table p =
  case p of
    (Class _ _ _ ifc _) -> aux ifc
    (Inst  _ _ imp _)   -> aux imp
  where
    aux :: Stmt -> Table.Map ID_Var Stmt
    aux s@(Var _ id _ (Match _ _ _ _ p _)) = Table.insert id s (aux p)
    aux s@(Var _ id _ p)                   = Table.insert id s (aux p)
    aux (Nop _)                            = Table.empty

err z = Ret z $ Error z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> String -> String -> [Stmt] -> Errors
errDeclared z str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing             -> []
            Just (Var _ _ tp _) ->
              case find (isInst (\id -> elem id (Type.getVs tp))) ids of
                Just _          -> []
                Nothing         -> err
            Just _              -> err
        where
          err = [toError z $ str ++ " '" ++ id ++ "' is already declared"]

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap aux $ map (\id->(id, find (isData $ (==)id) ids)) $ Type.getDs tp
    where
        aux (id, Nothing) = [toError z $ "data '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Class z (id,[var]) exts ifc p) = (esMe ++ esExts ++ esIfc ++ esP, ret) where
  esMe      = errDeclared z "interface" id ids
  (esP,p')  = stmt (s:ids) p  -- XXX: nao usar s p/ funcoes, usar cat
  (esIfc,_) = stmt ids ifc
  esExts    = concatMap f exts where
                f (sup,_) = case find (isClass $ (==)sup) ids of
                  Nothing -> [toError z $ "interface '" ++ sup ++ "' is not declared"]
                  Just _  -> []

  ret = cat ifc p'

  -- f, g, ..., p   (f,g,... may have type constraints)
  cat (Var z id tp (Match z2 False loc exp t f)) p =
    Var z id (constraint tp) (Match z2 False loc exp (cat t p) f)
  cat (Var z id tp q) p = Var z id (constraint tp) (cat q p)
  cat (Nop _) p         = p

  constraint Type0                      = Type0
  constraint (TypeD x)                  = TypeD x
  constraint (TypeN l)                  = TypeN $ map constraint l
  constraint (TypeF inp out)            = TypeF (constraint inp) (constraint out)
  constraint (TypeV var' l) | var==var' = TypeV var' (id:l)
                            | otherwise = TypeV var' l

stmt ids (Class _ (id,vars) _ _ _) = error "not implemented: multiple vars"

stmt ids s@(Inst z (id,[inst_tp]) imp p) = (es ++ esP ++ esImp, ret) where
  (esP,p')     = stmt (s'++ids) p   -- XXX: nao usar s p/ funcoes, usar cat
  (esImp,imp') = stmt (s : filter (not . (isClass $ (==)id)) ids) imp
                         -- prevent clashes w/ own class

  (ret, s', es) =
    case find (isClass $ (==)id) ids of
      -- class is not declared
      Nothing -> (p', [], [toError z $ "interface '" ++ id ++ "' is not declared"])

      -- class is declared
      Just cls@(Class _ (_,[clss_var]) exts ifc _) ->

        case find isSameInst ids of
          -- instance is already declared
          Just _  -> (p', [], [toError z $ "instance '" ++ id ++ " (" ++ intercalate "," [Type.show' inst_tp] ++ ")' is already declared"])

          -- instance is not declared
          Nothing -> (ret, [s], es1++ex++ey++ez) where

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

            hcls  = clssinst2table cls
            hinst = clssinst2table (Inst z (id,[inst_tp]) imp' (Nop z))

            -- funcs in cls (w/o default impl) not in inst
            ex = concatMap f $ Table.keys $ Table.difference (Table.filter g hcls) hinst where
                    f id = [toError z $ "missing implementation of '" ++ id ++ "'"]
                    g (Var _ _ _ (Match _ _ _ _ _ _)) = False
                    g _                               = True

            -- funcs in inst not in cls
            ey = concatMap f $ Table.keys $ Table.difference hinst hcls where
                    f id = [toError z $ "unexpected implementation of '" ++ id ++ "'"]

            -- funcs in both: check sigs // check impls
            ez = concat $ Table.elems $ Table.intersectionWith f hcls hinst where
                    f (Var _ _ tp1 _) (Var z2 id2 tp2 imp) =
                      case relates SUP tp1 tp2 of
                        Left es -> map (toError z2) es
                        Right (_,insts) ->
                          let tp' = Type.instantiate insts (TypeV clss_var []) in
                            if tp' == inst_tp then
                              []
                            else
                              [toError z $ "types do not match : expected '" ++
                                (Type.show' inst_tp) ++ "' : found '" ++
                                (Type.show' tp') ++ "'"]
                      ++
                      case imp of
                        Match _ _ _ _ _ _ -> []
                        otherwise         -> [toError z2 $ "missing implementation of '" ++ id2 ++ "'"]

            ---------------------------------------------------------------------

            ret = foldr f p' imps where
              imps = Table.elems $ Table.union (Table.map ((,) True)  hinst) -- prefer instance implementations
                                           (Table.map ((,) False) hcls)

              -- instance implementation:
              -- body -> (f1,f2,...)<-(f1_tp,f2_tp,...) ; body
              f :: (Bool,Stmt) -> Stmt -> Stmt
              f (True, Var z1 id1 tp1 (Match z2 False (LVar id2) exp _ e2)) acc
                | (id1 == id2) =
                  Var z1 (id1++"__"++Type.show' tp1) tp1
                    (Match z2 False (LVar $ id2++"__"++Type.show' tp1)
                                    (wrap tp1 exp)
                                    acc e2)
              f (True, Var _ _ _ _) acc = acc -- TODO: to pass tests

              -- class implementation:
              -- body -> (f1,f2,...)<-(f1_tp,f2_tp,...) ; f_default()
              f (False,  Var z id tp _) acc =
                Var z (id ++ "__" ++ Type.show' tp') tp
                  (Match z False (LVar $ id ++ "__" ++ Type.show' tp')
                    (wrap tp' $ Read z id)
                    acc (err z))
                where
                  tp' = Type.instantiate [(clss_var,inst_tp)] tp

              wrap :: Type -> Exp -> Exp
              wrap tp body = Func z tp $
                              foldr f (Ret z $ Call z body (Read z "_arg"))
                                $ map snd $ filter fst imps
                where
                  f (Var z id tp _) acc =
                    Var z id tp
                      (Match z False (LVar id)
                        (Read z (id++"__"++Type.show' tp))
                        acc
                        (err z))

          -----------------------------------------------------------------------

        where
          isSameInst (Inst _ (id',[tp']) _ _) = (id==id' && [inst_tp]==[tp'])
          isSameInst _                        = False

stmt ids (Inst _ (_,tps) _ _) = error "not implemented: multiple types"

stmt ids s@(Data z hr [] flds abs p) = (es_dcl ++ (errDeclared z "data" (Type.hier2str hr) ids) ++ es,
                                        s')
  where
    s'             = Data z hr [] flds' abs p'
    (es,p')        = stmt (s':ids) p
    (flds',es_dcl) =
      case Type.getSuper (TypeD hr) of
        Nothing          -> (flds, [])
        Just (TypeD sup) -> (Type.cat sups flds,
                             (getErrsTypesDeclared z ids (TypeD sup)) ++
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
                                ids' = Table.elems $ Table.unions $ map clssinst2table $ filter (isClass $ const True) ids

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
                                                      txp  = TypeD ["Int",show v]
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
            txp       = TypeD hr
            str       = Type.hier2str hr
            (tpd,esd) = case find (isData $ (==)str) ids of
              Just (Data _ _ _ tp _ _) -> (tp,    [])
              Nothing                  -> (TypeT, [toError z $ "data '" ++ str ++ "' is not declared"])

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
            (ese,mexp) = f (SUB,TypeN $ map (const $ TypeV "?" []) ls) tpexp
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
                            replicate (length ls - length exps) (Left $ TypeV "?" [])
                    ls'   = ls ++ replicate (length exps - length ls) LAny

                  -- (a,b,c) <- x
                  otherwise -> (ls', tps', \_->mexp) where
                    tps' = map Left tps ++
                           replicate (length ls - length tps) (Left $ TypeV "?" [])
                    ls'  = ls ++ replicate (length tps - length ls) LAny
                    tps  = case type_ $ getAnn $ fromJust mexp of
                      (TypeN x) -> x
                      x         -> [x]

              -- (k, (a,b,c)) <- x
              Left tp -> (ls', tps', \_->Nothing) where
                tps' = map Left tps ++
                       replicate (length ls - length tps) (Left $ TypeV "?" [])
                ls'  = ls ++ replicate (length tps - length ls) LAny
                tps  = case fromLeft tpexp of
                  (TypeN x) -> x
                  x         -> [x]

stmt ids (CallS z exp) = (ese++esf, CallS z exp') where
                         (ese, exp') = expr z (SUP, TypeV "?" []) ids exp
                         esf = case exp' of
                          Call _ _ _ -> []
                          otherwise  -> [toError z "expected call"]

-------------------------------------------------------------------------------


{-
stmt ids (If z exp p1 p2)   = (ese ++ es1 ++ es2, If z exp' p1' p2')
                              where
                                (ese,exp') = expr z (TypeD ["Bool"]) ids exp
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
  (es1, exp') = expr' (rel,bool (TypeV "?" []) txp (rel==SUP)) ids exp
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
expr' _       _   (Number z v)     = ([], Number z{type_=TypeD ["Int",show v]} v)
expr' _       _   (Unit   z)       = ([], Unit   z{type_=Type0})
expr' (_,txp) _   (Arg    z)       = ([], Arg    z{type_=txp})
expr' _       ids (Func   z tp p)  = (es, Func   z{type_=tp} tp p')
                                     where
                                      (es,p') = stmt ids p

expr' _ ids (Cons  z hr exp) = (es++es_exp, Cons z{type_=(TypeD hr)} hr exp')
    where
        hr_str = Type.hier2str hr
        (tp,es) = case find (isData $ (==)hr_str) ids of
            Nothing                      ->
              (TypeV "?" [], [toError z $ "data '" ++ hr_str ++ "' is not declared"])
            Just (Data _ _ _ tp True  _) ->
              (tp,        [toError z $ "data '" ++ hr_str ++ "' is abstract"])
            Just (Data _ _ _ tp False _) ->
              (tp,        [])
        (es_exp, exp') = expr z (SUP,tp) ids exp

expr' _ ids (Tuple z exps) = (es, Tuple z{type_=tps'} exps') where
                              rets :: [(Errors,Exp)]
                              rets  = map (\e -> expr z (SUP,TypeV "?" []) ids e) exps
                              es    = concat $ map fst rets
                              exps' = map snd rets
                              tps'  = TypeN (map (type_.getAnn) exps')

expr' (rel,txp) ids (Read z id) = (es, Read z{type_=tp} id') where
  (id', tp, es) =
    if id == "_INPUT" then
      (id, TypeD ["Int"], [])
    else
      -- find in top-level ids | id : a
      case find (isVar $ (==)id) ids of
        Just (Var _ _ tp _) -> (id, tp, [])   -- found
        Nothing             ->                -- not found
          -- find in classes | class X a with id : a
          case find (\(_,var) -> isJust var)            -- Just (clsI, Just (Var ...))
               $ map (\(cls,ids) -> (cls, find (isVar $ (==)id) ids)) -- [(cls1,Just (Var .)), .]
               $ map (\cls -> (cls, Table.elems $ clssinst2table cls)) -- [(cls1,ids1), ...]
               $ filter (isClass $ const True) ids              -- [cls1,cls2, ...]
            of
            -- not found
            Nothing -> (id, TypeV "?" [], [toError z $ "variable '" ++ id ++ "' is not declared"])

            -- find matching instance | id : a=<txp>
            Just pp@(Class _ (cls,[clss_var]) _ _ _, Just (Var _ id tp_var _)) ->
              case relates rel txp tp_var of
                Left  es        -> (id, TypeV "?" [], map (toError z) es)
                Right (_,insts) ->
                  let tp = Type.instantiate insts (TypeV clss_var []) in
                    if Type.isParametric tp then
                      (id, tp, [])  -- TODO: (TypeV "?") should be error
                    else
                      case find (isRel SUB tp . getTP) $ filter (isInst $ (==cls)) (sort' ids) of
                        Nothing -> (id, TypeV "?" [],
                                    [toError z $ "variable '" ++ id ++
                                     "' has no associated instance for data '" ++
                                     Type.show' txp ++ "' in class '" ++ cls ++ "'"])
                        Just (Inst _ (_,[inst_tp]) _ _) ->
                          (id ++ "__" ++ Type.show' tp', tp', []) where
                            tp' = Type.instantiate [(clss_var,inst_tp)] $ getTP $
                                    fromJust $ find (isVar $ (==)id)
                                                    (Table.elems $ clssinst2table (fst pp))
                          --case find (isVar $ (==)id) (Table.elems $ clssinst2table inst) of
                            --Just p  -> (getTP p, [])
                            --Nothing -> (getTP $ fromJust $ find (isVar $ (==)id) (Table.elems $ clssinst2table (fst pp)), [])
              where
                getTP (Inst _ (_,[tp]) _ _) = tp
                getTP (Var  _ _ tp _)       = tp
                sort' ids = ids -- TODO: sort by subtyping (topological order)

expr' (rel,txp) ids (Call z f exp) = (bool es_exp es_f (null es_exp),
                                     Call z{type_=tp_out} f' exp')
  where
    (es_exp, exp') = expr z (rel,TypeV "?" []) ids exp
    (es_f,   f')   = expr z (rel,TypeF (type_$getAnn$exp') txp) ids f

    tp_out = case type_ $ getAnn f' of
      TypeF _ out -> out
      otherwise   -> txp
