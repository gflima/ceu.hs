module Ceu.Grammar.TypeSys where

import Data.List (find, intercalate, unzip, unzip3, unzip4, isPrefixOf, elemIndex)
import Data.Maybe (isNothing, isJust, fromJust)
import Data.Bool (bool)
import Data.Either (isRight)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints as Cs  (Pair, cz, toList, hasClass)
import Ceu.Grammar.Type        as T   (Type(..), TypeC, show', sort', instantiate, getDs,
                                       getSuper, hier2str, isSupOfC,
                                       isRef, isRefC, toRef, toRefC, toDer, toDerC, toDerC',
                                       Relation(..), relatesC, isRelC, relatesErrorsC)
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic
import Ceu.Grammar.Match

--fromLeft  (Left  v) = v
--fromRight (Right v) = v

fst3 (x,_,_) = x
snd3 (_,x,_) = x
trd3 (_,_,x) = x

fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
trd4 (_,_,x,_) = x
fou4 (_,_,_,x) = x

checkFunc :: String -> Exp -> Errors
checkFunc str (EFunc  z FuncNested _ _) = [toError z str]
checkFunc str (ETuple _ l)              = concatMap (checkFunc str) l
checkFunc _   _                         = []

idtp id tp = "$" ++ id ++ "$" ++ T.show' tp ++ "$"

go :: Stmt -> (Errors, Stmt)
go p = (es,p') where
        (es,_,p') = stmt [[],[]] (TAny False "?",cz) p
        --(es,_,p') = f $ stmt [[],[]] (TAny False "?",cz) p where f (e,x,s) = traceShow s (e,x,s)
        --(es,_,p') = f $ stmt [[],[]] (TAny False "?",cz) p where f (e,x,s) = traceShow (show_stmt 0 s) (e,x,s)

-------------------------------------------------------------------------------

findVar :: Ann -> (ID_Var,Relation,TypeC) -> Envs -> Either Errors ((Int,Int,Bool), Stmt, (Type, [(ID_Var,Type)]))
findVar z x envs = g $ aux envs (0,undefined) where
  aux []         ret   = ret
  aux (env:envs) (n,_) = case findVar' z x env of
    Right (i,j)      -> (n, Right (getRef i, i, j))
    Left  (True, es) -> (n, Left  (True, es))          -- True = stop here with error
    Left  (False,es) -> aux envs (n+1, Left (False,es))

  g (_, Left  (_,ret))   = Left  ret
  g (n, Right (ref,i,j)) = Right ((length envs, n, ref), i, j)

  getRef :: Stmt -> Bool
  getRef (SVar _ _ tpc _) = T.isRefC tpc

findVar' :: Ann -> (ID_Var,Relation,TypeC) -> [Stmt] -> Either (Bool,Errors) (Stmt, (Type, [(ID_Var,Type)]))
findVar' z (id,rel,txpc) ids =   -- TODO: not currently using second return value
  case find f ids of
    Just s@(SVar _ _ tpc' _)   -> Right (s, ret) where
                                    Right ret = relatesC rel txpc (T.toDerC' tpc')
    Nothing ->
      case find (isVar id) ids of
        Nothing                -> Left (False, [toError z $ "variable '" ++ id ++ "' is not declared"])
        Just (SVar _ _ tpc' _) -> Left (True, map (toError z) es) where
                                    Left es = relatesC rel txpc (T.toDerC' tpc')
  where
    f (SVar _ id' tpc' _) = id==id' && (isRight $ relatesC rel txpc (T.toDerC' tpc'))
    f _                   = False

-------------------------------------------------------------------------------

supers :: [Stmt] -> Stmt -> [Stmt]
supers ids s@(SClass z _ ctrs ifc _) = s :
  case Cs.toList ctrs of
    [(_,[sup])] -> case find (isClass sup) ids of
                    Just x    -> supers ids x
                    otherwise -> []
    [(_,[])]    -> []
    otherwise   -> error "TODO: multiple vars, multiple constraints"

class2table :: [Stmt] -> Stmt -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
class2table ids cls = Map.unions $ map f1 (supers ids cls)
  where
    f1 (SClass _ _ _ ifc _) = f2 ifc
    f2 :: [(Ann,ID_Var,TypeC,Bool)] -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
    f2 ifc = Map.fromList $ map (\s@(_,id,_,_) -> (id,s)) ifc

inst2table :: [Stmt] -> Stmt -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
inst2table ids (SInst z cls tpc imp _) = Map.union (f2 imp) sups where
  sups =
    case find (isClass cls) ids of
      Just (SClass z _ ctrs _ _) ->
        case Cs.toList ctrs of
          [(_,sups)] -> Map.unions $ map f sups
          otherwise  -> error "TODO: multiple vars"

  f sup =
    case find pred ids of
      Just x  -> inst2table ids x
      Nothing -> Map.empty
    where
      pred (SInst  _ x y _ _) = (x==sup && y==tpc)
      pred _ = False

  f2 :: [(Ann,ID_Var,TypeC,Bool)] -> Map.Map ID_Var (Ann,ID_Var,TypeC,Bool)
  f2 ifc = Map.fromList $ map (\s@(_,id,_,_) -> (id,s)) ifc

-------------------------------------------------------------------------------

wrap insts (SVar z1 id1 (tp,_) (SSeq z2 (SMatch z3 True False body [(ds,EVar z4 id2,p)]) _)) acc | id1==id2 =
  SVar z1 id' (tp',cz)
    (SSeq z2
      (SMatch z3 True False body' [(ds,EVar z4 id',p)])
      acc)
  where
    id'   = idtp id1 tp'
    tp'   = T.instantiate insts tp
    body' = map_exp (Prelude.id,Prelude.id,ftp) body
      where
        ftp (tp,_) = (T.instantiate insts tp,cz)

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
        f (SInst _ cls' (_,ctrs') _ _) = (cls == cls') && (lvl>0 || null ctrs')
        f _                            = False

        g :: Stmt -> TypeC
        g (SInst _ _ tpc _ _) = tpc  -- types to instantiate

        -- expand types with constraints to multiple types
        -- TODO: currently refuse another level of constraints
        -- Int    -> [Int]
        -- X of a -> [X of Int, ...]
        h :: TypeC -> [Type]
        h tpc@(tp, ctrs) = if null ctrs then [tp] else insts where
          tpss  = combos' (lvl-1) ids (map Set.toList $ Map.elems ctrs)
          insts = map (flip T.instantiate tp) $ map (zip (Map.keys ctrs)) tpss

-------------------------------------------------------------------------------

fPat :: Envs -> Bool -> Exp -> (Errors,FuncType,TypeC,Exp)
fPat ids ini (EAny   z)     = ([], FuncGlobal, (TAny False "?",cz), EAny z)
fPat ids ini (EUnit  z)     = ([], FuncGlobal, (TUnit False,   cz), EUnit z)
fPat ids ini (EVar   z id)  = case findVar z (id,SUP,(TAny False "?",cz)) ids of
                                Right (lnr, SVar _ _ tpc _, _) -> ([], funcType' lnr, tpc', exp') where
                                                                    (tpc',exp') = toRef tpc (EVar z id)
                                Left  es                       -> (es, FuncGlobal, (TAny False "?",cz), EVar z id)
                              where
                                toRef tpc exp = if not $ isRefC tpc then
                                                  (tpc,exp)
                                                else if ini then
                                                  (tpc,ERefIni z exp)
                                                else
                                                  (T.toDerC tpc, ERefDer z{typec=T.toDerC tpc} exp)

fPat ids ini (ECons  z h)   = (es, FuncGlobal, tp, ECons z{typec=tp} h) where
                                (es,tp) = case find (isData $ hier2str h) (concat ids) of
                                  Nothing -> ([toError z $ "data '" ++ (hier2str h) ++ "' is not declared"],
                                              (TData False [] [] (TAny False "?"),cz))
                                  Just (SData _ _ tp _ _) -> case tp of
                                    (TData False _ ofs st, ctrs) -> (es,tp') where
                                      tp' = (TData False (take 1 h) ofs st, ctrs)
                                      es  = []-- map (toError z) (relatesErrorsC SUB tp tp')
fPat ids ini (ETuple z ls)  = (concat ess, ftp, (TTuple False (map fst tps),cz), ETuple z ls') where   -- TODO: cz should be union of all snd
                                (ess, ftps, tps, ls') = unzip4 $ map (fPat ids ini) ls
                                ftp = foldr funcType FuncUnknown ftps
fPat ids ini (ECall  z f e) = (esf++ese, funcType ftp1 ftp2, (tp',ctrs), ECall z f' e') where
                                (esf,ftp1,tpf,f') = fPat ids ini f
                                --(esf,f')   = expr z (SUP,(TAny False "?",cz)) ids f
                                (ese,ftp2,e') = expr z (SUP,(TAny False "?",cz)) ids e
                                (tp,ctrs) = typec $ getAnn f'
                                tp'       = case tp of
                                  TFunc False _ tp -> tp
                                  tp         -> tp
fPat ids ini (EExp   z e)   = (es, ftp, tpc, EExp z e') where
                                (es,ftp,tpc,e') = fPat ids ini e

-------------------------------------------------------------------------------

err z = SRet z $ EError z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> Maybe (Stmt->Bool) -> String -> String -> [Stmt] -> Errors
errDeclared z chk str id ids =
    if (take 1 id == "_") || (take 1 id == "$") then [] else    -- nested _ret, __and (par/and)
        case find (isAny id) ids of
            Nothing                      -> []
            Just s@(SVar _ _ (_,ctrs) _) ->
              if chk' s then [] else
                case find (isInst (\id -> Cs.hasClass id ctrs)) ids of
                  Just _                 -> []
                  Nothing                -> err
            Just _                       -> err
        where
          err = [toError z $ str ++ " '" ++ id ++ "' is already declared"]

          chk' = case chk of
            Nothing -> const False
            Just f  -> f

          isInst  f (SInst  _ id _ _ _)   = f id
          isInst  _  _                    = False

          isAny :: String -> Stmt -> Bool
          isAny id s = isClass id s || isData id s || isVar id s

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z ids tp = concatMap f (T.getDs tp) where
  f :: Type -> Errors
  f (TData _ hier _ tp_) = case find (isData id) ids of
    Nothing                  -> [toError z $ "data '" ++ id ++ "' is not declared"]
    Just (SData _ _ tp' _ _) -> [] --relatesErrorsC SUP tp' (tp_,cz)
-- TODO
    where
      id = hier2str hier

-------------------------------------------------------------------------------

stmt :: Envs -> TypeC -> Stmt -> (Errors, FuncType, Stmt)

stmt ids tpr s@(SClass z id ctrs ifc p) = (esMe ++ esExts ++ es, ftp, p') where
  esMe    = errDeclared z Nothing "constraint" id (concat ids)
  esExts  = case Cs.toList ctrs of
              [(_,sups)] -> concatMap f sups where
                f sup = case find (isClass sup) (concat ids) of
                  Nothing -> [toError z $ "constraint '" ++ sup ++ "' is not declared"]
                  Just _  -> []
              otherwise  -> error "TODO: multiple vars"
  (es,ftp,p') = stmt (envsAdd ids s) tpr p

stmt ids tpr s@(SInst z cls xxx@(itp,ictrs) imp p) = (es ++ esP, ftp, p'') where
  (esP, ftp, p'') = stmt (envsAdd ids s) tpr p'
  (p', es)  =
    case find (isClass cls) (concat ids) of
      -- class is not declared
      Nothing -> (p, [toError z $ "constraint '" ++ cls ++ "' is not declared"])

      -- class is declared
      Just k@(SClass _ _ ctrs ifc _) -> case Cs.toList ctrs of
        [(clss_var,sups)] ->
          case find isSameInst (concat ids) of
            -- instance is already declared
            Just _  -> (p, [toError z $ "instance '" ++ cls ++ " (" ++ intercalate "," [T.show' itp] ++ ")' is already declared"])

            -- instance is not declared
            Nothing -> (p2, es1++ex++ey++ez) where

              hcls   = class2table (concat ids) k
              hinst  = inst2table  (concat ids) s

              ---------------------------------------------------------------------

              -- check extends
              --  constraint      (Eq  for a)
              --  instance (Eq  for Bool)                  <-- so Bool must implement Eq
              --  constraint      (Ord for a) extends (Eq for a)  <-- but Ord extends Eq
              --  instance (Ord for Bool)                  <-- Bool implements Ord
              es1 = concatMap f sups where
                f sup = case find (isInstOf sup xxx) (concat ids) of
                  Nothing -> [toError z $ "instance '" ++ sup ++ " for " ++
                              (T.show' itp) ++ "' is not declared"]
                  Just _  -> []
                isInstOf x y (SInst _ x' y' _ _) = (x'==x && y' `T.isSupOfC` y)
                isInstOf _ _ _                   = False

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
                        case relatesC SUP tp1 tp2 of
                          Left es -> map (toError z2) es
                          Right (_,insts) ->
                            let tp' = T.instantiate insts (TAny False clss_var) in
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
                cat f@(SVar _ id (_,ctrs) _) acc = foldr cat' acc itpss where
                  itpss :: [[Type]] -- only combos with new itp (others are already instantiated)
                  itpss = T.sort' $ combos' 1 (s:(concat ids)) (map Set.toList $ Map.elems $ ctrs)
                                     -- include this instance "s"
                  --itpss = filter (\l -> elem itp l) $ combos' 1 (s:ids) (map Set.toList $ Map.elems ctrs)
                  cat' :: [Type] -> Stmt -> Stmt
                  cat' itps acc = wrap (zip (Map.keys ctrs) itps) f acc

  -- TODO: relates deve levar em consideracao os ctrs (e depende da REL)
                -- functions to instantiate
                fs :: [Stmt]
                fs  = filter pred (concat ids) where
                        pred (SVar _ id1 tpc@(_,ctrs) (SSeq _ (SMatch _ True False body [(_,EVar _ id2,_)]) _)) =
                          id1==id2 && (not inInsts) && (Cs.hasClass cls ctrs) where
                            inInsts = not $ null $ Map.filter f hinst where
                                        f (_,id',tpc',_) = id1==id' && (isRight $ relatesC SUP tpc' tpc)
                                            -- see GenSpec:CASE-1
                        pred _ = False

              -- Prototype all HCLS as HINST signatures (not declared yet) before
              -- the implementations appear to prevent "undeclared" errors.
              p2 = foldr cat p1 fs where
                    cat (_,id,(tp,_),_) acc = foldr cat' acc itps where
                      cat' itp acc = SVar z (idtp id tp') (tp',cz) acc where
                        tp' = T.instantiate [(clss_var,itp)] tp

                    -- functions to instantiate
                    fs = Map.filter pred hcls where
                      pred (_,id,(tp,_),_) = isNothing $ find (isVar id') (concat ids) where
                        id' = idtp id tp'
                        tp' = T.instantiate [(clss_var,itp)] tp

                    -- follow concrete types from generic/constrained implementations:
                    --    instance of IEq for a where a implements IXx
                    itps :: [Type]
                    itps = map f $ combos (map g $ map Set.toList $ Map.elems ictrs) where
                      f :: [Type] -> Type
                      f tps = T.instantiate (zip (Map.keys ictrs) tps) itp
                      g :: [ID_Class] -> [Type]
                      g [ifc] = map f $ filter pred (concat ids) where
                                  pred (SInst _ icls _ _ _) = ifc==icls
                                  pred _                    = False
                                  f    (SInst _ _ (tp,_) _ _) = tp

          where
            isSameInst (SInst _ id (tp',_) _ _) = (cls==id && [itp]==[tp'])
            isSameInst _                        = False

        otherwise  -> error "TODO: multiple vars"

stmt ids tpr s@(SData z nms (tpD@(TData False hr _ st),cz) abs p) =
  (es_dcl ++ (errDeclared z Nothing "data" (T.hier2str hr) (concat ids)) ++ es,
  ftp,
  SData z nms (tpD,cz) abs p')
  where
    (es,ftp,p') = stmt (envsAdd ids s) tpr p
    es_dcl = (getErrsTypesDeclared z (concat ids) st) ++ case T.getSuper hr of
                Nothing  -> []
                Just sup -> (getErrsTypesDeclared z (concat ids) (TData False sup [] (TUnit False)))

stmt ids tpr s@(SVar z id tpc@(tp,ctrs) p) = (es_data ++ es_id ++ es, ftp, f p'') where
  es_data = getErrsTypesDeclared z (concat ids) tp
  es_id   = errDeclared z (Just chk) "variable" id (concat ids) where
              chk :: Stmt -> Bool
              chk (SVar _ id1 tpc'@(TFunc False _ _,_) (SMatch _ True False _ [(_,EVar _ id2,_)])) = (id1 /= id2)
              chk (SVar _ id1 tpc'@(TFunc False _ _,_) _) = (tpc == tpc') -- function prototype
              chk _ = False
  (es,ftp,p'') = stmt (envsAdd ids s) tpr p'

  -- In case of a parametric/generic var with a constraint, instantiate it for
  -- each instance of the constraint:
  --    f :: (a -> T) where a implements I
  -- <to>
  --    $f$X$
  --    $f$Y$
  --    ...
  (f,p') = if ctrs == cz then (SVar z id tpc, p) else -- normal concrete declarations
    case p of
      SSeq _ (SMatch z2 True False body [(_,EVar _ id',_)]) s
        | id==id' -> (Prelude.id, funcs s)    -- instantiate for all available implementations
      _   -> (Prelude.id, p)                  -- just ignore parametric declarations
      where
        funcs :: Stmt -> Stmt
        funcs p = foldr cat p (T.sort' $ combos' 1 (concat ids) (map Set.toList $ Map.elems ctrs)) where
                    cat :: [Type] -> Stmt -> Stmt
                    cat itps acc = wrap (zip (Map.keys ctrs) itps) s acc

-------------------------------------------------------------------------------

stmt envs tpr (SMatch z ini fce exp cses) = (es', funcType ftp1 ftp2, SMatch z ini fce exp' cses'') where
  es'                   = esc ++ escs ++ esem
  (ese, ftp1,exp')      = expr z (SUP,tpl) envs exp
  (escs,ftp2,tpl,cses') = (es, ftp, tpl, cses')
    where
      --(l1,l2) :: ( [(Errors,TypeC,Exp)] , [(Errors,Stmt)] )
      (l0,l1,l2) = unzip3 $ map f cses where
                    f (ds,pt,st) = ((es,ftp,ds'), fPat envs' ini pt, stmt envs' tpr st) where
                      (es,ftp,ds') = stmt envs tpr ds
                      envs' = (g ds' x):xs where
                                (x:xs) = envs
                                g   (SNop _)       env = env
                                g s@(SVar _ _ _ p) env = s : (g p env)

      es :: Errors
      es = concat $ (map fst3 l0) ++ (map fst4 l1) ++ (map fst3 l2)

      tpl :: TypeC
      tpl = trd4 $ l1 !! 0

      cses' :: [(Stmt,Exp,Stmt)]
      cses' = zip3 (map trd3 l0) (map fou4 l1) (map trd3 l2)

      ftp :: FuncType
      ftp = foldr funcType FuncUnknown $ (map snd3 l0) ++ (map snd4 l1) ++ (map snd3 l2)

  (ok, esm) = matchX (concat envs) (map snd3 cses') exp'
  esem      = bool esm ese (null esm)    -- hide ese if esm

  -- set  x <- 1    // fce=false
  -- set! 1 <- x    // fce=true
  -- if   1 <- x    // fce=true
  esc = if null esem then
          if fce then
            bool [] [toError z "match is exhaustive"] ok
          else
            bool [toError z "match is non exhaustive"]  [] ok
        else
          []

  cses'' = if not fce then cses' else
            cses' ++ [(SNop z, EAny z, SRet z $ EError z (-2))]

-------------------------------------------------------------------------------

stmt ids _   (SCall z exp)  = (ese++esf, ftp, SCall z exp') where
                                (ese,ftp,exp') = expr z (SUP, (TAny False "?",cz)) ids exp
                                esf = case exp' of
                                  ECall _ _ _ -> []
                                  otherwise  -> [toError z "expected call"]

stmt envs tpr (SSeq z p1 p2) = (es1++es2, funcType ftp1 ftp2, SSeq z p1' p2')
  where
    (es1,ftp1,p1') = stmt envs  tpr p1
    (es2,ftp2,p2') = stmt envs' tpr p2
    envs' = case p1' of
              (SMatch _ True False (EArg _) [_]) -> []:envs  -- add body environment after args assignment
              _ -> envs

stmt ids tpr (SLoop z p)    = (es, ftp, SLoop z p') where
                                (es,ftp,p') = stmt ids tpr p

stmt ids tpr (SRet z exp)   = (es ++ ese, ftp, SRet z exp') where
                                (es,ftp,exp') = expr z (SUP,tpr) ids exp
                                ese = checkFunc "cannot return nested function" exp'
{-
                                -- TODO: closures
                                xxx = f $ fst $ typec $ getAnn exp' where
                                  f (TFunc False _ _) = True
                                  f (TTuple False l)  = or $ map f l
                                  f _           = False
-}

stmt _   _   (SNop z)       = ([], FuncGlobal, SNop z)

-------------------------------------------------------------------------------

expr :: Ann -> (Relation,TypeC) -> Envs -> Exp -> (Errors, FuncType, Exp)
expr z (rel,txp) ids exp = (es1++es2, ftp, exp') where
  --(es1, exp') = expr' (rel,bool (TAny False "?" []) txp (rel/=ANY)) ids exp
  --(es1, exp') = expr' (rel,bool (TAny False "?" []) txp (rel==SUP)) ids exp
                           -- only force expected type on SUP
  (es1, ftp, exp') = expr' (rel,txp) ids exp
  es2 = if not.null $ es1 then [] else
          map (toError z) (relatesErrorsC rel txp (typec $ getAnn exp'))

  -- https://en.wikipedia.org/wiki/Subtyping
  -- SIf S is a subtype of T, the subtyping relation is often written S <: T,
  -- to mean that any term of type S can be safely used in a context where a
  -- term of type T is expected.
  --    txp = T :> S = exp'.type

-- TODO: use txp in the cases below:
--  * number: decide for float/int/etc
--  * cons:   ?
--  * tuple:  instantiate sub exps

expr' :: (Relation,TypeC) -> Envs -> Exp -> (Errors, FuncType, Exp)

expr' _       _   (EError  z v)     = ([], FuncGlobal, EError  z{typec=(TBot False,cz)} v)
expr' _       _   (EUnit   z)       = ([], FuncGlobal, EUnit   z{typec=(TUnit False,cz)})
expr' (_,txp) _   (EArg    z)       = ([], FuncGlobal, EArg    z{typec=txp})

expr' _ envs (EFunc z ftp1 tpc p) = (es, ftp, EFunc z{typec=tpc} ftp tpc p')
 where
  (es,ftp2,p') = stmt ([]:envs) (out,cs) p      -- add args environment, locals to be added on Match...EArg
  (TFunc False _ out,cs) = tpc
  ftp = if ftp1 == FuncUnknown then ftp2 else
          assertEq ftp1 ftp1 ftp2

expr' _ ids (EMatch z exp pat) = (esp++esem++esc, funcType ftp1 ftp2,
                                  EMatch z{typec=(TData False ["Bool"] [] (TUnit False),cz)} exp' pat')
  where
    (esp,ftp1,tpp,pat') = fPat ids False pat
    (ese,ftp2,exp')     = expr z (SUP,tpp) ids exp
    (ok, esm)           = (ok, map (toError z) esm) where (ok,esm) = matchX (concat ids) [pat'] exp'
    esem                = bool esm ese (null esm)    -- hide ese if esm
    esc = if null esem then
            bool [] [toError z "match is exhaustive"] ok
          else
            []

expr' _ ids (EField z hr fld) = (es, FuncGlobal, EVar z{typec=(TFunc False inp out,cz)} (hr_str ++ "." ++ fld))
  where
    hr_str = T.hier2str hr

    (inp,out,cz,es) = case find (isData hr_str) (concat ids) of
      Nothing -> (TAny False "?",TAny False "?",cz, [toError z $ "data '" ++ hr_str ++ "' is not declared"])
      Just (SData _ nms (tpc@(TData False _ _ (TTuple False sts)),cz) _ _) -> (tpc,out,cz,es) where (out,es) = f nms sts
      Just (SData _ nms (tpc@(TData False _ _ st),cz) _ _)                 -> (tpc,out,cz,es) where (out,es) = f nms [st]

    f nms sts = case fld of
      ('_':idx) -> if length sts >= idx' then
                    (sts!!(idx'-1), [])
                   else
                    (TAny False "?",      [toError z $ "field '" ++ fld ++ "' is not declared"])
                   where
                    idx' = read idx
      otherwise -> case (nms, elemIndex fld (fromJust nms)) of
                    (Nothing, _)  -> (TAny False "?", [toError z $ "field '" ++ fld ++ "' is not declared"])
                    (_, Nothing)  -> (TAny False "?", [toError z $ "field '" ++ fld ++ "' is not declared"])
                    (_, Just idx) -> (sts!!idx, [])

expr' (rel,txp) ids (ECons z hr) = (es1++es2, FuncGlobal, ECons z{typec=tpc2} hr)
  where
    hr_str = T.hier2str hr
    (tpc1,es1) = case find (isData hr_str) (concat ids) of
      Nothing                     -> ((TAny False "?",cz),
                                      [toError z $ "data '" ++ hr_str ++ "' is not declared"])
      Just (SData _ _ tpc True  _) -> (f tpc, [toError z $ "data '" ++ hr_str ++ "' is abstract"])
      Just (SData _ _ tpc False _) -> (f tpc, [])

    f (tp@(TData False _ ofs (TUnit False)), ctrs) = (tp,            ctrs)
    f (tp@(TData False _ ofs tpst),          ctrs) = (TFunc False tpst tp, ctrs)

    (es2,tpc2) = case relatesC SUP txp tpc1 of
      Left es      -> (map (toError z) es,tpc1)
      Right (tp,_) -> ([],(tp,ctrs)) where (_,ctrs)=tpc1

expr' _ ids (ETuple z exps) = (es, ftp, ETuple z{typec=(tps',cz)} exps') where
                              rets :: [(Errors,FuncType,Exp)]
                              rets  = map (\e -> expr z (SUP,(TAny False "?",cz)) ids e) exps
                              es    = concat $ map fst3 rets
                              exps' = map trd3 rets
                              tps'  = TTuple False (map (fst.typec.getAnn) exps')
                              ftp   = foldr funcType FuncUnknown $ map snd3 rets

expr' (rel,txp@(txp_,cxp)) ids (EVar z id) = (es, funcType' lnr, toDer $ EVar z{typec=tpc} id') where    -- EVar x
  (id', tpc, lnr, es)
    | (id == "_INPUT") = (id, (TData False ["Int"] [] (TUnit False),cz), (0,0,False), [])
    | otherwise        =
      -- find in top-level ids | id : a
      case findVar z (id,rel,txp) ids of
        Left  es -> (id, (TAny False "?",cz), (0,0,False), es)
        Right (lnr, SVar _ id' tpc@(_,ctrs) _,_) ->
          if ctrs == cz then
            (id, tpc, lnr, [])
          else
            case find pred (concat ids) of            -- find instance
              Just (SVar _ _ tpc@(tp,ctrs) _) ->
                if null ctrs then
                  (idtp id tp, tpc, lnr, [])
                else
                  if null cxp then
                    (id, (TAny False "?",cz), lnr, err)
                  else
                    (id, tpc, lnr, [])
              Nothing -> (id, (TAny False "?",cz), lnr, err)
            where
              pred :: Stmt -> Bool
              pred (SVar _ k tpc@(tp,_) _) = (idtp id tp == k) && (isRight $ relatesC SUP txp tpc)
              pred _                       = False

              err = [toError z $ "variable '" ++ id ++
                     "' has no associated instance for '" ++
                     T.show' txp_ ++ "'"]

  toDer exp = if not $ T.isRefC tpc then exp else
                ERefDer z{typec=T.toDerC tpc} exp
              where
                tpc = typec $ getAnn exp

expr' (rel,txpC) ids (ERefRef z exp) = (es, ftp, ERefRef z{typec=T.toRefC $ typec $ getAnn exp'} exp')
  where
    (es, ftp, exp') = expr z (rel,T.toDerC' txpC) ids exp

expr' (rel,(txp_,cxp)) ids (ECall z f exp) = (bool ese esf (null ese) ++ esa,
                                              funcType ftp1 ftp2,
                                              ECall z{typec=tpc_out} f' exp')
  where
    (ese, ftp1, exp') = expr z (rel, (TAny False "?",cz)) ids exp
    (esf, ftp2, f')   = expr z (rel, (TFunc False (fst$typec$getAnn$exp') txp_, cxp)) ids f
                                      -- TODO: ctrs of exp'

    tpc_out = case typec $ getAnn f' of
      (TFunc False _ out_,ctrs) -> (out_,ctrs)
      otherwise           -> (txp_,cxp)

    esa = checkFunc "cannot pass nested function" exp'

expr' (_,txp) ids (EAny z) = ([], FuncGlobal, EAny z{typec=txp})

--expr' _ _ e = error $ show e
