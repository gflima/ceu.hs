module Ceu.Grammar.TypeSys where

import Debug.Trace
import Data.List (find, intercalate, unfoldr, unzip4, sortBy)
import Data.Maybe (isJust, fromJust)
import Data.Bool (bool)
import Data.Either (isRight)
import qualified Data.Map as Table
import qualified Data.Set as Set

import Ceu.Grammar.Globals
import Ceu.Grammar.Type as Type (Type(..), show', instantiate, getDs, getVs', getSuper,
                                 cat, hier2str, hasVs,
                                 Relation(..), relates, isRel, relatesErrors)
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic

fromLeft (Left v) = v

idtp id tp = "__" ++ id ++ "__" ++ Type.show' tp

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

class2table :: [Stmt] -> Stmt -> Table.Map ID_Var Stmt
class2table ids (Class z (_,[var]) exts ifc _) =
  case exts of
    [(sid,_)] -> Table.union super (aux ifc) where
                  super = case find (isClass $ (==)sid) ids of
                    Just x    -> class2table ids x
                    otherwise -> Table.empty
    []        -> aux ifc
  where
    aux :: Stmt -> Table.Map ID_Var Stmt
    aux s@(Var _ id _ (Match _ _ _ _ p _)) = Table.insert id s (aux p)
    aux s@(Var _ id _ p)                   = Table.insert id s (aux p)
    aux (Nop _)                            = Table.empty

inst2table :: [Stmt] -> Stmt -> Table.Map ID_Var Stmt
inst2table ids (Inst z (cls,[tp]) imp _) = Table.union (aux imp) sups where
  sups =
    case find (isClass $ (==)cls) ids of
      Just (Class z _ exts _ _) -> Table.unions $ map f exts

  f (cls',_) =
    case find pred ids of
      Just x  -> inst2table ids x
      Nothing -> Table.empty
    where
      pred (Inst  _ (x,[y]) _ _) = (x==cls' && y==tp)
      pred _ = False

  aux :: Stmt -> Table.Map ID_Var Stmt
  aux s@(Var _ id _ (Match _ _ _ _ p _)) = Table.insert id s (aux p)
  --aux s@(Var _ id _ p)                   = Table.insert id s (aux p)
  aux (Nop _)                            = Table.empty

err z = Ret z $ Error z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> Maybe (Stmt->Bool) -> String -> String -> [Stmt] -> Errors
errDeclared z chk str id ids =
    if (take 1 id == "_") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing               -> []
            Just s@(Var _ _ tp _) ->
              if chk' s then [] else
                case find (isInst (\id -> elem id (Type.getVs' tp))) ids of
                  Just _          -> []
                  Nothing         -> err
            Just _                -> err
        where
          err = [toError z $ str ++ " '" ++ id ++ "' is already declared"]
          chk' = case chk of
            Nothing -> const False
            Just f  -> f

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap aux $ map (\id->(id, find (isData $ (==)id) ids)) $ Set.toList $ Type.getDs tp
    where
        aux (id, Nothing) = [toError z $ "data '" ++ id ++ "' is not declared"]
        aux (_,  Just _)  = []

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Class z (id,[var]) exts ifc p) = (esMe ++ esExts ++ es, p') where
  esMe    = errDeclared z Nothing "interface" id ids
  esExts  = concatMap f exts where
              f (sup,_) = case find (isClass $ (==)sup) ids of
                Nothing -> [toError z $ "interface '" ++ sup ++ "' is not declared"]
                Just _  -> []
  (es,p') = stmt (s:ids) (cat ifc p)

  -- f, g, ..., p   (f,g,... may have type constraints)
  cat (Var z id tp (Match z2 False (LVar id') exp t f)) p | id==id' =
    Var z id (constraint tp) (Match z2 False (LVar id') exp (cat t p) f)
  cat (Var z id tp q) p =
    Var z id (constraint tp) (cat q p)
  cat (Nop _) p = p

  constraint Type0                      = Type0
  constraint (TypeD x)                  = TypeD x
  constraint (TypeN l)                  = TypeN $ map constraint l
  constraint (TypeF inp out)            = TypeF (constraint inp) (constraint out)
  constraint (TypeV var' l) | var==var' = TypeV var' (id:l)
                            | otherwise = TypeV var' l

stmt ids (Class _ (id,vars) _ _ _) = error "not implemented: multiple vars"

stmt ids s@(Inst z (id,[inst_tp]) imp p) = (es ++ esP, p'') where
  (esP, p'') = stmt (s:ids) p'
  (p',  es)  =
    case find (isClass $ (==)id) ids of
      -- class is not declared
      Nothing -> (p, [toError z $ "interface '" ++ id ++ "' is not declared"])

      -- class is declared
      Just cls@(Class _ (_,[clss_var]) exts ifc _) ->

        case find isSameInst ids of
          -- instance is already declared
          Just _  -> (p, [toError z $ "implementation '" ++ id ++ " (" ++ intercalate "," [Type.show' inst_tp] ++ ")' is already declared"])

          -- instance is not declared
          Nothing -> (p''', es1++ex++ey++ez) where

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

            hcls  = class2table ids cls
            hinst = inst2table  ids s
            p'    = cat1 imp p
            p''   = foldr cat2 p'  (Table.elems $ Table.difference hcls hinst) --(Table.elems hcls)
            p'''  = foldr cat3 p'' (Table.elems hcls)

            ---------------------------------------------------------------------

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
                          let tp' = Type.instantiate insts (TypeV clss_var [id]) in
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


            ---------------------------------------------------------------------

            -- instance implementation:
            -- body ==> (f1,f2,...)<-(f1_tp,f2_tp,...) ; body
            cat1 s@(Var z id tp (Match z2 False (LVar _) exp t f)) p =
              Var z id' tp
                (Match z2 False (LVar id')
                  (wrap tp exp)
                  (cat1 t p) f)
              where
                id' = idtp id tp
            cat1 (Nop _) p = p
            --cat1 x p = error $ show x

            -- class implementation:
            -- body -> (f1,f2,...)<-(f1_tp,f2_tp,...) ; f_a()
            cat2 (Var z id tp (Match _ _ _ _ _ _)) acc =
              Var z (idtp id tp') tp'
                (Match z False (LVar $ idtp id tp')
                  (wrap tp $ Read z (idtp id tp))
                  acc (err z))
              where
                tp' = Type.instantiate [(clss_var,inst_tp)] tp
            cat2 (Var z id tp _) acc = acc            -- no class impl. either

            wrap :: Type -> Exp -> Exp
            wrap tp body = Func z tp $
                            foldr f (Ret z $ Call z body (Arg z)) (Table.elems hcls)
              where
                f (Var z id tp _) acc =
                  Match z False (LVar id)
                    (Read z (idtp id (Type.instantiate [(clss_var,inst_tp)] tp)))
                    acc
                    (err z)

            -- prototypes
            cat3 (Var z id tp _) acc =
              Var z (idtp id tp') tp' acc
              where
                tp' = Type.instantiate [(clss_var,inst_tp)] tp

        where
          isSameInst (Inst _ (id',[tp']) _ _) = (id==id' && [inst_tp]==[tp'])
          isSameInst _                        = False

stmt ids (Inst _ (_,tps) _ _) = error "not implemented: multiple types"

stmt ids s@(Data z hr [] flds abs p) = (es_dcl ++ (errDeclared z Nothing "data" (Type.hier2str hr) ids) ++ es,
                                        s' p')
  where
    s'             = Data z hr [] flds' abs
    (es,p')        = stmt ((s' (Nop annz)):ids) p
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

stmt ids s@(Var  z id tp p) = (es_data ++ es_id ++ es, Var z id tp p'') where
  es_data = getErrsTypesDeclared z ids tp
  es_id   = errDeclared z (Just chk) "variable" id ids where
              chk :: Stmt -> Bool
              chk (Var _ id1 tp'@(TypeF _ _) (Match _ False (LVar id2) _ _ _)) = (id1 /= id2)
              chk (Var _ id1 tp'@(TypeF _ _) _) = (tp == tp') -- function prototype
              chk _ = False
  (es,p'') = stmt (s:ids) p'

  p' = if take 2 id == "__" then p else
    case Set.toList $ Type.getVs' tp of
      []    -> p
      [cls] -> case p of
        Match z2 False (LVar id') exp t f
          | id==id'   -> Var z (idtp id tp) tp (Match z2 False (LVar $ idtp id tp) exp t f)
          | otherwise -> p
        _             -> p

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
              Nothing               -> (TypeV "?" [], [toError z $ "variable '" ++ var ++ "' is not declared"])
            (ese,mexp) = f (SUP,tpl) tpexp
        (LExp e)     -> (True, es++ese, LExp e', mexp)
          where
            (ese,mexp) = f (SUP, type_ $ getAnn e') tpexp
            (es, e')   = expr z (SUP,TypeV "?" []) ids e

        (LCons hr l) -> (fchk txp mexp tpexp || chk1, esd++esl++es'++ese, LCons hr l', mexp)
          where
            txp       = TypeD hr
            str       = Type.hier2str hr
            (tpd,esd) = case find (isData $ (==)str) ids of
              Just (Data _ _ _ tp _ _) -> (tp,    [])
              Nothing                  -> (TypeV "?" [], [toError z $ "data '" ++ str ++ "' is not declared"])

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
                                (es,exp') = expr z (SUP,TypeV "?" []) ids exp
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
  (id', tp, es)
    | (id == "_INPUT") = (id, TypeD ["Int"], [])
    | otherwise        =
      -- find in top-level ids | id : a
      case find (isVar $ (==)id) ids of
        Nothing             -> (id, TypeV "?" [], [toError z $ "variable '" ++ id ++ "' is not declared"])
        Just (Var _ _ tp _) ->
          case relates rel txp tp of
            Left  es      -> (id, TypeV "?" [], map (toError z) es)
            Right (tp',_) -> if take 2 id == "__" then (id, tp, []) else
              case Set.toList $ Type.getVs' tp' of
                []    -> (id, tp, [])
                [cls] ->  -- TODO: single cls
                  case find pred ids of
{-
-- now we check the implementations
                    Nothing -> (id, TypeV "?" [],
                                [toError z $ "variable '" ++ id ++
                                 "' has no associated implementation for data '" ++
                                 Type.show' txp ++ "' in interface '" ++ cls ++ "'"])
                               where
                                [cls] = Set.toList $ Type.getVs' tp'  -- TODO: single cls
-}
                    Just (Var _ _ tp'' _) -> (id', tp'', []) where
                                              id' = if Type.hasVs tp'' then
                                                      id
                                                    else
                                                      idtp id tp''
                  where
                    pred :: Stmt -> Bool
                    pred (Var _ _ tp _) = isRight $ relates SUP txp tp
                    pred _              = False

expr' (rel,txp) ids (Call z f exp) = (bool es_exp es_f (null es_exp),
                                     Call z{type_=tp_out} f' exp')
  where
    (es_exp, exp') = expr z (rel,TypeV "?" []) ids exp
    (es_f,   f')   = expr z (rel,TypeF (type_$getAnn$exp') txp) ids f

    tp_out = case type_ $ getAnn f' of
      TypeF _ out -> out
      otherwise   -> txp
