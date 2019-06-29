module Ceu.Grammar.TypeSys where

import Data.List (find, intercalate, unzip, unzip3, isPrefixOf)
import Data.Maybe (isNothing, isJust, fromJust)
import Data.Bool (bool)
import Data.Either (isRight)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints as Cs  (Pair, cz, toList, hasClass)
import Ceu.Grammar.Type        as T   (Type(..), TypeC, show', sort', instantiate, getDs,
                                       getSuper, hier2str, isSupOf,
                                       Relation(..), relates, isRel, relatesErrors)
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic

fromLeft (Left v) = v

idtp id tp = "$" ++ id ++ "$" ++ T.show' tp ++ "$"

go :: Stmt -> (Errors, Stmt)
go p = stmt [] p
--go p = f $ stmt [] p where f (e,s) = traceShow s (e,s)
--go p = f $ stmt [] p where f (e,s) = traceShow (show_stmt 0 s) (e,s)

-------------------------------------------------------------------------------

isClass f (Class _ id _ _ _)    = f id
isClass _  _                    = False

isInst  f (Inst  _ id _ _ _)    = f id
isInst  _  _                    = False

isData  f (Data  _ (TypeD hr _ _,_) _ _) = f (T.hier2str hr)
isData  _  _                           = False

isVar   f (Var   _ id _ _)      = f id
isVar   _  _                    = False

isAny :: (String -> Bool) -> Stmt -> Bool
isAny f s = isClass f s || isData f s || isVar f s

findVar :: Ann -> (ID_Var,Relation,TypeC) -> [Stmt] -> Either Errors (Stmt, (Type, [(ID_Var,Type)]))
findVar z (id,rel,txp) ids =
  case find f ids of
    Just s@(Var _ _ tp' _)   -> Right (s, ret) where
                                  Right ret = relates rel txp tp'
    Nothing ->
      case find (isVar $ (==)id) ids of
        Nothing              -> Left $ [toError z $ "variable '" ++ id ++ "' is not declared"]
        Just (Var _ _ tp' _) -> Left $ map (toError z) es where
                                  Left es = relates rel txp tp'
  where
    f (Var _ id' tp' _) = id==id' && (isRight $ relates rel txp tp')
    f _                 = False

supers :: [Stmt] -> Stmt -> [Stmt]
supers ids s@(Class z _ ctrs ifc _) = s :
  case Cs.toList ctrs of
    [(_,[sup])] -> case find (isClass $ (==)sup) ids of
                    Just x    -> supers ids x
                    otherwise -> []
    [(_,[])]    -> []
    otherwise   -> error "TODO: multiple vars, multiple constraints"

class2table :: [Stmt] -> Stmt -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
class2table ids cls = Map.unions $ map f1 (supers ids cls)
  where
    f1 (Class _ _ _ ifc _) = f2 ifc
    f2 :: [(Ann,ID_Var,TypeC,Bool)] -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
    f2 ifc = Map.fromList $ map (\s@(_,id,_,_) -> (id,s)) ifc

inst2table :: [Stmt] -> Stmt -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
inst2table ids (Inst z cls tp imp _) = Map.union (f2 imp) sups where
  sups =
    case find (isClass $ (==)cls) ids of
      Just (Class z _ ctrs _ _) ->
        case Cs.toList ctrs of
          [(_,sups)] -> Map.unions $ map f sups
          otherwise  -> error "TODO: multiple vars"

  f sup =
    case find pred ids of
      Just x  -> inst2table ids x
      Nothing -> Map.empty
    where
      pred (Inst  _ x y _ _) = (x==sup && y==tp)
      pred _ = False

  f2 :: [(Ann,ID_Var,TypeC,Bool)] -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
  f2 ifc = Map.fromList $ map (\s@(_,id,_,_) -> (id,s)) ifc

wrap insts (Var z id1 (tp_,_) (Match _ False (LVar id2) body _ _)) acc | id1==id2 =
  Var z id' (tp_',cz)
    (Match z False (LVar id')
      body'
      acc
      (err z))
  where
    id'   = idtp id1 tp_'
    tp_'  = T.instantiate insts tp_
    body' = map_exp (Prelude.id,Prelude.id,ftp) body
      where
        ftp (tp_,_) = (T.instantiate insts tp_,cz)

-- All possible combinations between members of each group:
--    G1        G2        G3
-- [ [1,10], [2,20,200], [3], ... ]
-- [ [1,2,3,...], [1,20,3,...], [1,200,3,...], ... ]
combos :: [[a]] -> [[a]]
combos l = foldr g [[]] l where
    g :: [a] -> [[a]] -> [[a]]
    g l combos = foldr (\v acc -> (h v combos) ++ acc) [] l

    h :: a -> [[a]] -> [[a]]
    h v combos = map (\combo -> v:combo) combos

-- [ [Ia], [Ib], ... ]
-- [ [A1,A2,...], [B1,B2,...], ... ]
-- [ [A1,B1,...], [A1,B2,...], ... ]
combos' :: Int -> [Stmt] -> [[ID_Class]] -> [[Type]]
combos' lvl ids clss = combos insts where
  insts :: [[Type]]
  insts = map h clss
    where
      h :: [ID_Class] -> [Type]
      h [cls] = concatMap h $ map g $ filter f ids where
        f :: Stmt -> Bool
        f (Inst _ cls' (_,ctrs') _ _) = (cls == cls') && (lvl>0 || null ctrs')
        f _                           = False

        g :: Stmt -> TypeC
        g (Inst _ _ tp _ _) = tp  -- types to instantiate

        -- expand types with constraints to multiple types
        -- TODO: currently refuse another level of constraints
        -- Int    -> [Int]
        -- X of a -> [X of Int, ...]
        h :: TypeC -> [Type]
        h tp@(tp_, ctrs) = if null ctrs then [tp_] else insts where
          tpss  = combos' (lvl-1) ids (map Set.toList $ Map.elems ctrs)
          insts = map (flip T.instantiate tp_) $ map (zip (Map.keys ctrs)) tpss

err z = Ret z $ Error z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> Maybe (Stmt->Bool) -> String -> String -> [Stmt] -> Errors
errDeclared z chk str id ids =
    if (take 1 id == "_") || (take 1 id == "$") then [] else    -- nested _ret, __and (par/and)
        case find (isAny $ (==)id) ids of
            Nothing                 -> []
            Just s@(Var _ _ (_,ctrs) _) ->
              if chk' s then [] else
                case find (isInst (\id -> Cs.hasClass id ctrs)) ids of
                  Just _          -> []
                  Nothing         -> err
            Just _                -> err
        where
          err = [toError z $ str ++ " '" ++ id ++ "' is already declared"]
          chk' = case chk of
            Nothing -> const False
            Just f  -> f

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap f (T.getDs tp) where
  f :: Type -> Errors
  f (TypeD hier _ tp_) = case find (isData $ (==)id) ids of
    Nothing               -> [toError z $ "data '" ++ id ++ "' is not declared"]
    Just (Data _ tp' _ _) -> [] --relatesErrors SUP tp' (tp_,cz)
-- TODO
    where
      id = hier2str hier

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> (Errors, Stmt)

stmt ids s@(Class z id ctrs ifc p) = (esMe ++ esExts ++ es, p') where
  esMe    = errDeclared z Nothing "constraint" id ids
  esExts  = case Cs.toList ctrs of
              [(_,sups)] -> concatMap f sups where
                f sup = case find (isClass $ (==)sup) ids of
                  Nothing -> [toError z $ "constraint '" ++ sup ++ "' is not declared"]
                  Just _  -> []
              otherwise  -> error "TODO: multiple vars"
  (es,p') = stmt (s:ids) p

stmt ids s@(Inst z cls xxx@(itp,ictrs) imp p) = (es ++ esP, p'') where
  (esP, p'') = stmt (s:ids) p'
  (p',  es)  =
    case find (isClass $ (==)cls) ids of
      -- class is not declared
      Nothing -> (p, [toError z $ "constraint '" ++ cls ++ "' is not declared"])

      -- class is declared
      Just k@(Class _ _ ctrs ifc _) -> case Cs.toList ctrs of
        [(clss_var,sups)] ->
          case find isSameInst ids of
            -- instance is already declared
            Just _  -> (p, [toError z $ "instance '" ++ cls ++ " (" ++ intercalate "," [T.show' itp] ++ ")' is already declared"])

            -- instance is not declared
            Nothing -> (p2, es1++ex++ey++ez) where

              hcls   = class2table ids k
              hinst  = inst2table  ids s

              ---------------------------------------------------------------------

              -- check extends
              --  constraint      (Eq  for a)
              --  instance (Eq  for Bool)                  <-- so Bool must implement Eq
              --  constraint      (Ord for a) extends (Eq for a)  <-- but Ord extends Eq
              --  instance (Ord for Bool)                  <-- Bool implements Ord
              es1 = concatMap f sups where
                f sup = case find (isInstOf sup xxx) ids of
                  Nothing -> [toError z $ "instance '" ++ sup ++ " for " ++
                              (T.show' itp) ++ "' is not declared"]
                  Just _  -> []
                isInstOf x y (Inst _ x' y' _ _) = (x'==x && y' `T.isSupOf` y)
                isInstOf _ _ _                  = False

              ---------------------------------------------------------------------

              -- funcs in cls (w/o default impl) not in inst
              ex = concatMap f $ Map.keys $ Map.difference (Map.filter g hcls) hinst where
                      f id = [toError z $ "missing instance of '" ++ id ++ "'"]
                      g (_,_,_,impl) = not impl

              -- funcs in inst not in cls
              ey = concatMap f $ Map.keys $ Map.difference hinst hcls where
                      f id = [toError z $ "unexpected instance of '" ++ id ++ "'"]

              -- funcs in both: check sigs // check impls
              ez = concat $ Map.elems $ Map.intersectionWith f hcls hinst where
                      f (_,_,tp1,_) (z2,id2,tp2,impl) =
                        case relates SUP tp1 tp2 of
                          Left es -> map (toError z2) es
                          Right (_,insts) ->
                            let tp' = T.instantiate insts (TypeV clss_var) in
                              if tp' == itp then
                                []
                              else
                                [toError z $ "types do not match : expected '" ++
                                  (T.show' itp) ++ "' : found '" ++
                                  (T.show' tp') ++ "'"]
                        ++ (bool [toError z2 $ "missing instance of '" ++ id2 ++ "'"] [] impl)

              ---------------------------------------------------------------------

              -- Take each generic function with CLS constraint and instantiate
              -- it with HINST type.
              -- Either from default implementations in HCLS or from generic
              -- functions:
              --    constraint IEq for a with
              --      var eq  : ((a,a) -> Int)
              --      func neq (x,y) : ((a,a) -> Int) do ... eq(a,a) ... end              -- THIS
              --    end
              --    func f x : (a -> Int) where a implements IEq do ... eq(a,a) ... end   -- THIS
              --    instance of IEq for Int with
              --      func eq (x,y) : ((Int,Int) -> Int) do ... end
              --    end
              -- <to>
              --    $neq$Int$ ...
              --    $f$Int$ ...
              -- HINST does not have `neq`, so we will copy it from HCLS,
              -- instantiate with the instance type, changing all HCLS
              -- with HINST type.
              p1 = foldr cat p fs where
                cat :: Stmt -> Stmt -> Stmt
                cat f@(Var _ id (_,ctrs) _) acc = foldr cat' acc itpss where
                  itpss :: [[Type]] -- only combos with new itp (others are already instantiated)
                  itpss = T.sort' $ combos' 1 (s:ids) (map Set.toList $ Map.elems $ ctrs)
                                     -- include this instance "s"
                  --itpss = filter (\l -> elem itp l) $ combos' 1 (s:ids) (map Set.toList $ Map.elems ctrs)
                  cat' :: [Type] -> Stmt -> Stmt
                  cat' itps acc = wrap (zip (Map.keys ctrs) itps) f acc

  -- TODO: relates deve levar em consideracao os ctrs (e depende da REL)
                -- functions to instantiate
                fs :: [Stmt]
                fs  = filter pred ids where
                        pred (Var _ id1 tp@(_,ctrs) (Match _ False (LVar id2) body _ _)) =
                          id1==id2 && (not inInsts) && (Cs.hasClass cls ctrs) where
                            inInsts = not $ null $ Map.filter f hinst where
                                        f (_,id',tp',_) = id1==id' && (isRight $ relates SUP tp' tp)
                                            -- see GenSpec:CASE-1
                        pred _ = False

              -- Prototype all HCLS as HINST signatures (not declared yet) before
              -- the implementations appear to prevent "undeclared" errors.
              p2 = foldr cat p1 fs where
                    cat (_,id,(tp,_),_) acc = foldr cat' acc itps where
                      cat' itp acc = Var z (idtp id tp') (tp',cz) acc where
                        tp' = T.instantiate [(clss_var,itp)] tp

                    -- functions to instantiate
                    fs = Map.filter pred hcls where
                      pred (_,id,(tp,_),_) = isNothing $ find (isVar $ (==)id') ids where
                        id' = idtp id tp'
                        tp' = T.instantiate [(clss_var,itp)] tp

                    -- follow concrete types from generic/constrained implementations:
                    --    instance of IEq for a where a implements IXx
                    itps :: [Type]
                    itps = map f $ combos (map g $ map Set.toList $ Map.elems ictrs) where
                      f :: [Type] -> Type
                      f tps = T.instantiate (zip (Map.keys ictrs) tps) itp
                      g :: [ID_Class] -> [Type]
                      g [ifc] = map f $ filter pred ids where
                                  pred (Inst _ icls _ _ _) = ifc==icls
                                  pred _                   = False
                                  f    (Inst _ _ (tp,_) _ _) = tp

          where
            isSameInst (Inst _ id (tp',_) _ _) = (cls==id && [itp]==[tp'])
            isSameInst _                       = False

        otherwise  -> error "TODO: multiple vars"

stmt ids s@(Data z tp@(TypeD hr _ st,_) abs p) = (es_dcl ++ (errDeclared z Nothing "data" (T.hier2str hr) ids) ++ es,
                                                     Data z tp abs p')
  where
    (es,p') = stmt (s:ids) p
    es_dcl  = case T.getSuper hr of
                Nothing  -> []
                Just sup -> (getErrsTypesDeclared z ids (TypeD sup [] Type0)) ++
                            (getErrsTypesDeclared z ids st)

stmt ids s@(Var z id tp@(tp_,ctrs) p) = (es_data ++ es_id ++ es, f p'') where
  es_data = getErrsTypesDeclared z ids tp_
  es_id   = errDeclared z (Just chk) "variable" id ids where
              chk :: Stmt -> Bool
              chk (Var _ id1 tp'@(TypeF _ _,_) (Match _ False (LVar id2) _ _ _)) = (id1 /= id2)
              chk (Var _ id1 tp'@(TypeF _ _,_) _) = (tp == tp') -- function prototype
              chk _ = False
  (es,p'') = stmt (s:ids) p'

  -- In case of a parametric/generic var with a constraint, instantiate it for
  -- each instance of the constraint:
  --    f :: (a -> T) where a implements I
  -- <to>
  --    $f$X$
  --    $f$Y$
  --    ...
  (f,p') = if ctrs == cz then (Var z id tp, p) else -- normal concrete declarations
    case p of
      Match z2 False (LVar id') body t f
        | id==id' -> (Prelude.id, funcs t)    -- instantiate for all available implementations
      _   -> (Prelude.id, p)                  -- just ignore parametric declarations
      where
        funcs :: Stmt -> Stmt
        funcs p = foldr cat p (T.sort' $ combos' 1 ids (map Set.toList $ Map.elems ctrs)) where
                    cat :: [Type] -> Stmt -> Stmt
                    cat itps acc = wrap (zip (Map.keys ctrs) itps) s acc

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

stmt ids (Match z chk loc exp p1 p2) = (es', Match z chk loc' exp' p1' p2') where
  es'              = esl ++ esc ++ esem ++ es1 ++ es2
  (esl, tpl, loc') = fLoc loc
  (es1, p1')       = stmt ids p1
  (es2, p2')       = stmt ids p2
  (ese, exp')      = expr z (SUP,tpl) ids exp
  (may, esm)       = match loc' exp'
  esem             = bool esm ese (null esm)    -- hide ese if esm

  -----------------------------------------------------------------------------

  -- set  x <- 1    // chk=false
  -- set! 1 <- x    // chk=true
  -- if   1 <- x    // chk=true
  esc = if null esem then
          if chk then
            bool [toError z "match never fails"] [] may
          else
            bool [toError z "match might fail"]  [] (not may)
        else
          []

  -----------------------------------------------------------------------------

  fLoc :: Loc -> (Errors,TypeC,Loc)
  fLoc LAny          = ([], (TypeV "?",cz), LAny)
  fLoc LUnit         = ([], (Type0,    cz), LUnit)
  fLoc (LVar    id)  = case find (isVar $ (==)id) ids of
                        Just (Var _ _ tp _) -> ([], tp, LVar id)
                        otherwise           -> ([toError z $ "variable '" ++ id ++ "' is not declared"],
                                                (TypeV "?",cz), LVar id)
  fLoc (LNumber v)   = ([], (TypeD ["Int"] [] Type0, cz), LNumber v)
  fLoc (LCons   h l) = (esl++esh, tph, LCons h l') where
                        (esl,(tpl,csl),l') = fLoc l
                        (esh,tph) = case find (isData $ (==)(hier2str h)) ids of
                          Nothing -> ([toError z $ "data '" ++ (hier2str h) ++ "' is not declared"],
                                      (TypeD [] [] (TypeV "?"),cz))
                          Just (Data _ tp _ _) -> case tp of
                            (TypeD _ ofs _, ctrs) -> (es,tp') where
                              tp' = (TypeD (take 1 h) ofs tpl, csl)
                              es  = map (toError z) (relatesErrors SUB tp tp')
  fLoc (LTuple  ls)  = (concat ess, (TypeN (map fst tps),cz), LTuple ls') where   -- TODO: cz should be union of all snd
                        (ess, tps, ls') = unzip3 $ map fLoc ls
  fLoc (LExp    e)   = (ese, type_ $ getAnn e', LExp e') where
                        (ese,e') = expr z (SUP,(TypeV "?",cz)) ids e

  --tLoc :: Loc -> TypeC
  --tLoc loc = tp where (_,tp,_) = fLoc loc

  -----------------------------------------------------------------------------

  -- Match must be covariant on variables and contravariant on constants:
  --  LVar    a     <- x      # assign # a     SUP x
  --  LExp    a     <- x      # match  # a     SUP x
  --  LAny          <- x      # match  # BOT   SUB x
  --  LUnit         <- x      # match  # unit  SUB x
  --  LNumber a     <- x      # match  # Int.X SUB x
  --  LCons   a b   <- Cons x # match  # a     SUP Cons x | b match x
  --  LCons   a.* b <- x      # match  # a     SUP x      | b match x
  --  LTuple  (a,b) <- (x,y)  # match  # (B,B) SUB (x,y)  | a match x,  b match y
  --  LTuple  (a,b) <- x      # match  # (B,B) SUB x      | a match x1, b match x2

  match :: Loc -> Exp -> (Bool, Errors)

  match _               (Arg _)        = (False, [])

  -- structural match
  match LUnit           (Unit   _)     = (False, [])
  match (LNumber v1)    (Number _ v2)  = (False, es) where
                                          es = bool [toError z "match never succeeds : constant mismatch"] [] (v1==v2)
  match (LCons hr1 loc)
        (Call _ (Cons z hr2) exp)      = (may, es++es') where
                                          es = if hr1 `isPrefixOf` hr2 then [] else
                                                [toError z "match never succeeds : constructor mismatch"]
                                          (may, es') = match loc exp
  match (LTuple ls)     (Tuple z exps) = (or mays, concat eses ++ es) where
                                          es = if lenl == lene then [] else
                                                [toError z "match never succeeds : arity mismatch"]
                                          (mays, eses) = unzip $ zipWith match ls' exps' where
                                            ls'   = ls   ++ replicate (lene - lenl) LAny
                                            exps' = exps ++ replicate (lenl - lene) (Error z (-2))
                                          lenl  = length ls
                                          lene  = length exps
  match l@(LCons _ _)   e@(Cons z _)    = match l (Call z e (Unit z))

  -- structural fail
  match l e | (isL l && isE e) = (False, ["match never succeeds"]) where
    isL LUnit       = True
    isL (LNumber _) = True
    isL (LCons _ _) = True
    isL (LTuple _)  = True
    isL _           = False

    isE (Unit   _)   = True
    isE (Number _ _) = True
    isE (Tuple  _ _) = True
    isE (Cons   _ _) = True
    isE (Call   _ (Cons _ _) _) = True
    isE _            = False

  -- contravariant on constants (SUB)
  match LUnit           exp            = (True, es) where
                                          es = map (toError $ getAnn exp)
                                                   (relatesErrors SUB (Type0,cz) (type_ $ getAnn exp))
  match (LNumber v)     exp            = (True, es) where
                                          es = map (toError $ getAnn exp)
                                                   (relatesErrors SUB (TypeD ["Int",show v] [] Type0,cz) (type_ $ getAnn exp))

  -- non-constants: LAny,LVar (no fail) // LExp (may fail)
  match (LVar _)        _              = (False, [])
  match LAny            _              = (False, [])
  match (LExp _)        _              = (True,  [])

  -- rec
  match loc             exp            = match' loc (type_ $ getAnn exp) where

    z = getAnn exp

    match' :: Loc -> TypeC -> (Bool, Errors)
    match' LUnit        tp  = (False, es) where
                                es = [] --map (toError z) (relatesErrors SUB (Type0,cz) tp)
    match' (LNumber v)   tp = (True, es) where
                                es = map (toError z) (relatesErrors SUB (TypeD ["Int",show v] [] Type0,cz) tp)
    match' (LVar _)      _  = (False, [])
    match' LAny          _  = (False, [])
    match' (LExp _)      _  = (True,  [])
    match' (LCons hr1 l) tp = case tp of
                              (TypeD hr2 _ st, ctrs) -> (may' || may, es) where
                                                          may'     = (hr2 `isPrefixOf` hr1) && (hr1 /= hr2)
                                                          (may,es) = match' l (st,ctrs)
                              otherwise            -> (False, [])
    match' (LTuple ls)  tp = case tp of
                              (TypeN tps, ctrs)    -> (or mays, concat ess) where
                                                        (mays, ess) = unzip $ zipWith match' ls (map f tps)
                                                        f tp = (tp,ctrs)
                              otherwise            -> (False, [])

-------------------------------------------------------------------------------

stmt ids (CallS z exp) = (ese++esf, CallS z exp') where
                         (ese, exp') = expr z (SUP, (TypeV "?",cz)) ids exp
                         esf = case exp' of
                          Call _ _ _ -> []
                          otherwise  -> [toError z "expected call"]

stmt ids (Seq z p1 p2)      = (es1++es2, Seq z p1' p2')
                              where
                                (es1,p1') = stmt ids p1
                                (es2,p2') = stmt ids p2
stmt ids (Loop z p)         = (es, Loop z p')
                              where
                                (es,p') = stmt ids p

stmt ids (Ret z exp)        = (es, Ret z exp')
                              where
                                (es,exp') = expr z (SUP,(TypeV "?",cz)) ids exp
                                  -- VAR: I expect exp.type to be a subtype of Top (any type)

stmt _   (Nop z)            = ([], Nop z)

-------------------------------------------------------------------------------

expr :: Ann -> (Relation,TypeC) -> [Stmt] -> Exp -> (Errors, Exp)
expr z (rel,txp) ids exp = (es1++es2, exp') where
  --(es1, exp') = expr' (rel,bool (TypeV "?" []) txp (rel/=ANY)) ids exp
  --(es1, exp') = expr' (rel,bool (TypeV "?" []) txp (rel==SUP)) ids exp
                           -- only force expected type on SUP
  (es1, exp') = expr' (rel,txp) ids exp
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

expr' :: (Relation,TypeC) -> [Stmt] -> Exp -> (Errors, Exp)

expr' _       _   (Error  z v)     = ([], Error  z{type_=(TypeB,cz)} v)
expr' _       _   (Number z v)     = ([], Number z{type_=(TypeD ["Int",show v] [] Type0,cz)} v)
expr' _       _   (Unit   z)       = ([], Unit   z{type_=(Type0,cz)})
expr' (_,txp) _   (Arg    z)       = ([], Arg    z{type_=txp})
expr' _       ids (Func   z tp p)  = (es, Func   z{type_=tp} tp p')
                                     where
                                      (es,p') = stmt ids p

expr' _ ids (Cons z hr) = (es, Cons z{type_=tp} hr)
    where
        hr_str = T.hier2str hr
        (tp,es) = case find (isData $ (==)hr_str) ids of
            Nothing                  -> ((TypeV "?",cz),
                                         [toError z $ "data '" ++ hr_str ++ "' is not declared"])
            Just (Data _ tp True  _) -> (f tp, [toError z $ "data '" ++ hr_str ++ "' is abstract"])
            Just (Data _ tp False _) -> (f tp, [])

        f (tp_@(TypeD _ ofs Type0), ctrs) = (tp_,            ctrs)
        f (tp_@(TypeD _ ofs tpst),  ctrs) = (TypeF tpst tp_, ctrs)


expr' _ ids (Tuple z exps) = (es, Tuple z{type_=(tps',cz)} exps') where
                              rets :: [(Errors,Exp)]
                              rets  = map (\e -> expr z (SUP,(TypeV "?",cz)) ids e) exps
                              es    = concat $ map fst rets
                              exps' = map snd rets
                              tps'  = TypeN (map (fst.type_.getAnn) exps')

expr' (rel,txp@(txp_,cxp)) ids (Read z id) = (es, Read z{type_=tp} id') where    -- Read x
  (id', tp, es)
    | (id == "_INPUT") = (id, (TypeD ["Int"] [] Type0,cz), [])
    | otherwise        =
      -- find in top-level ids | id : a
      case findVar z (id,rel,txp) ids of
        Left  es -> (id, (TypeV "?",cz), es)
        Right (Var _ id' tp@(_,ctrs) _,(tp',_)) ->
          if ctrs == cz then (id, tp, []) else
            --[] | tp==tp' -> (id, tp, [])
               -- | otherwise -> error $ show (id, tp, tp')
               -- | otherwise -> (id, tp, [])
            case find pred ids of            -- find instance
              Just (Var _ _ tp''@(tp_'',ctrs) _) ->
                if null ctrs then
                  (idtp id tp_'', tp'', [])
                else
                  if null cxp then
                    (id, (TypeV "?",cz), err)
                  else
                    (id, tp'', [])
              Nothing -> (id, (TypeV "?",cz), err)
            where
              pred :: Stmt -> Bool
              pred (Var _ k tp@(tp_,_) _) = (idtp id tp_ == k) && (isRight $ relates SUP txp tp)
              pred _                      = False

              err = [toError z $ "variable '" ++ id ++
                     "' has no associated instance for '" ++
                     T.show' txp_ ++ "'"]

expr' (rel,(txp_,cxp)) ids (Call z f exp) = (bool es_exp es_f (null es_exp),
                                             Call z{type_=tp_out} f' exp')
  where
    (es_exp, exp') = expr z (rel, (TypeV "?",cz)) ids exp
    (es_f,   f')   = expr z (rel, (TypeF (fst$type_$getAnn$exp') txp_, cxp)) ids f
                                  -- TODO: ctrs of exp'

    tp_out = case type_ $ getAnn f' of
      (TypeF _ out_,ctrs) -> (out_,ctrs)
      otherwise           -> (txp_,cxp)
