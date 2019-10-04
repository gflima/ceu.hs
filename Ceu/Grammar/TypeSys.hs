module Ceu.Grammar.TypeSys where

import Data.List (sort, find, intercalate, unzip, unzip3, unzip4, isPrefixOf, elemIndex)
import Data.Maybe (isNothing, isJust, fromJust)
import Data.Bool (bool)
import Data.Either (isRight)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Ceu.Trace
import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints as Cs (cz)
import Ceu.Grammar.Type        as T
import Ceu.Grammar.Ann
import Ceu.Grammar.Basic
import Ceu.Grammar.Match

fromLeft  (Left  v) = v
--fromRight (Right v) = v

fst3 (x,_,_) = x
snd3 (_,x,_) = x
trd3 (_,_,x) = x

fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
trd4 (_,_,x,_) = x
fou4 (_,_,_,x) = x

checkFuncNested :: String -> Exp -> Errors
checkFuncNested str (EFunc  z (TFunc FuncNested _ _,_) _ _) = toErrors z str
checkFuncNested str (ETuple _ l)                            = concatMap (checkFuncNested str) l
checkFuncNested _   _                                       = []

go :: Stmt -> (Errors, Stmt)
go p = (es,p') where
        (es,_,_,p') = stmt [[]] (TAny,cz) p
        --(es,_,_,p') = f $ stmt [[]] (TVar False "?",cz) p where f (e,x,y,s) = traceShow s (e,x,y,s)
        --(es,_,_,p') = f $ stmt [[]] (TVar False "?",cz) p where f (e,x,y,s) = traceShow (show_stmt 0 s) (e,x,y,s)

-------------------------------------------------------------------------------

findVars :: Ann -> ID_Var -> Envs -> Either Errors [((Bool,Int), Stmt)]
findVars z id (env:envs) =
  case (envs, findVars' z id env) of
    (_,  Right xs)         -> Right $ map (\x -> ((getRef x, length envs), x)) xs
    (_,  Left  (True, es)) -> Left es          -- True = stop here with error
    ([], Left  (False,es)) -> Left es
    (_,  Left  (False,es)) -> findVars z id envs
  where
    getRef :: Stmt -> Bool
    getRef (SVar _ _ tpc _) = T.isRefC tpc

findVars' :: Ann -> ID_Var -> [Stmt] -> Either (Bool,Errors) [Stmt]
findVars' z id envs =
  case filter f envs of   -- ignore errors from '_' special identifiers
    [] -> Left (False, toErrors' z id $ "variable '" ++ id ++ "' is not declared")
    xs -> Right xs
  where
    f (SVar _ id' tpc' _) = id==id'
    f _                   = False

-------------------------------------------------------------------------------

fPat :: Envs -> Bool -> Exp -> (Errors,FT_Ups,TypeC,Exp)
fPat envs ini (EAny   z)     = ([], (FuncGlobal,Nothing), (TAny, cz), EAny z)
fPat envs ini (EUnit  z)     = ([], (FuncGlobal,Nothing), (TUnit,cz), EUnit z)
fPat envs ini (EVar   z id)  =
  case findVars z id envs of
    Left  es -> (es, (FuncGlobal,Nothing), (TAny,cz), EVar z id)
    Right (((ref,n), SVar _ _ tpc _) : _) ->  -- latest definition
      ([], ftReq (length envs) (id,ref,n), tpc', exp')
        where
          (tpc',exp') = toRef tpc (EVar z id)
          toRef tpc exp = if not $ (T.isRefableRefC tpc) then
                            (tpc,exp)
                          else if ini then
                            (tpc,ERefIni z exp)
                          else
                            (T.toDerC tpc, ERefDer z{typec=T.toDerC tpc} exp)

fPat envs ini (ECons  z h)   = (es, (FuncGlobal,Nothing), tp, ECons z{typec=tp} h) where
                                (es,tp) = case find (isData $ hier2str h) (concat envs) of
                                  Nothing -> (toErrors z $ "data '" ++ (hier2str h) ++ "' is not declared",
                                              (TData False [] [],cz))
                                  Just (SData _ tp _ st cs _ _) -> case tp of
                                    TData False _ ofs -> (es,(tp',cs)) where
                                      tp' = f (TData False (take 1 h) ofs) st
                                      es  = []-- map (toErrors z) (relatesErrorsC SUB tp tp')

                                      f tdat TUnit = tdat
                                      f tdat st    = TFunc FuncGlobal st tdat

fPat envs ini (ETuple z ls)  = (concat ess, ft, (TTuple (map fst tps),cz), ETuple z ls') where   -- TODO: cz should be union of all snd
                                (ess, fts, tps, ls') = unzip4 $ map (fPat envs ini) ls
                                ft = foldr ftMin (FuncUnknown,Nothing) fts

fPat envs ini (ECall  z f e) = (esf++ese, ftMin ft1 ft2, (tp',cs), ECall z f' e') where
                                (esf,ft1,tpf,f') = fPat envs ini f
                                (ese,ft2,_,e')   = expr z (SUP,(TAny,cz)) envs e
                                (tp,cs) = typec $ getAnn f'
                                tp'     = case tp of
                                  TFunc _ _ tp -> tp
                                  tp           -> tp

fPat envs ini (EExp   z e)   = (es, ft, tpc, EExp z e') where
                                (es,ft,tpc,e') = fPat envs ini e

-------------------------------------------------------------------------------

err z = SRet z $ EError z (-2)  -- TODO: -2

-------------------------------------------------------------------------------

errDeclared :: Ann -> Maybe (Stmt->Bool) -> String -> String -> [Stmt] -> Errors
errDeclared z chk str id envs =
    if (take 1 id == "_") || (take 1 id == "$") then [] else    -- nested _ret, __and (par/and)
        case find (isAny id) envs of
            Nothing                    -> []
            Just s@(SVar _ _ (_,cs) _) -> if chk' s then [] else err
            Just _                      -> err
        where
          err = toErrors z $ str ++ " '" ++ id ++ "' is already declared"

          chk' = case chk of
            Nothing -> const False
            Just f  -> f

          isAny :: String -> Stmt -> Bool
          isAny id s = isData id s || isVar id s

getErrsTypesDeclared :: Ann -> [Stmt] -> Type -> Errors
getErrsTypesDeclared z envs tp = concatMap f (T.getDs tp) where
  f :: Type -> Errors
  f (TData _ hier _) = case find (isData id) envs of
    Nothing                    -> toErrors' z id $ "data '" ++ id ++ "' is not declared"
    Just (SData _ _ _ _ _ _ _) -> [] --relatesErrorsC SUP tp' (tp_,cz)
-- TODO
    where
      id = hier2str hier

-------------------------------------------------------------------------------

                                          -- am I a global, nested or closure?
                                                    -- nested closures inside me
stmt :: Envs -> TypeC -> Stmt -> (Errors, FT_Ups, [FuncType], Stmt)

stmt envs tpr s@(SData z tpD@(TData False hr _) nms st cz abs p) =
  (es_dcl ++ (errDeclared z Nothing "data" (T.hier2str hr) (concat envs)) ++ es,
  ft, fts,
  SData z tpD nms st cz abs p')
  where
    envs' = envsAdd envs s
    (es,ft,fts,p') = stmt envs' tpr p
    es_dcl = (getErrsTypesDeclared z (concat envs') st) ++ case T.getSuper hr of
                Nothing  -> []
                Just sup -> (getErrsTypesDeclared z (concat envs) (TData False sup []))

stmt envs tpr s@(SVar z id tpc@(tp,cs) p) = (es_data ++ es_id ++ es, ft, fts, SVar z id tpc p') where
  es_data = getErrsTypesDeclared z (concat envs) tp
  es_id   = errDeclared z (Just chk) "variable" id (concat envs) where
              chk :: Stmt -> Bool
              chk (SVar _ id1      (TFunc _ _ _,_) (SMatch _ True False _ [(_,EVar _ id2,_)])) = (id1 /= id2)
              chk (SVar _ _   tpc'@(TFunc _ _ _,_) _) = (tpc == tpc') -- function prototype
              chk _ = False

  (es,ft,fts,p') = stmt (envsAdd envs s) tpr p

-------------------------------------------------------------------------------

stmt envs tpr (SMatch z ini fce exp cses) = (es', ftMin ft1 ft2, fts1++fts2, SMatch z ini fce exp' cses'') where
  es'                  = esc ++ escs ++ esem
  (ese, ft1,fts1,exp') = expr z (SUP,tpl) envs exp
  (escs,ft2,fts2,tpl,cses') = (es, ft, fts, tpl, cses')
    where
      --(l1,l2) :: ( [(Errors,TypeC,Exp)] , [(Errors,Stmt)] )
      (l0,l1,l2) = unzip3 $ map f cses where
                    f (ds,pt,st) = ((es,ft,fts,ds'), fPat envs' ini pt, stmt envs' tpr st) where
                      (es,ft,fts,ds') = stmt envs tpr ds
                      envs' = (g ds' x):xs where
                                (x:xs) = envs
                                g   (SNop _)         env = env
                                g s@(SVar _ _ _ p) env = s : (g p env)

      es :: Errors
      es = concat $ (map fst4 l0) ++ (map fst4 l1) ++ (map fst4 l2)

      tpl :: TypeC
      tpl = trd4 $ l1 !! 0

      cses' :: [(Stmt,Exp,Stmt)]
      cses' = zip3 (map fou4 l0) (map fou4 l1) (map fou4 l2)

      ft :: FT_Ups
      ft = foldr ftMin (FuncUnknown,Nothing) $ (map snd4 l0) ++ (map snd4 l1) ++ (map snd4 l2)

      fts :: [FuncType]
      fts = concatMap trd4 l0 ++ concatMap trd4 l2

  (ok, esm) = matchX (concat envs) (map snd3 cses') exp'
  esem      = bool esm ese (null esm)    -- hide ese if esm

  -- set  x <- 1    // fce=false
  -- set! 1 <- x    // fce=true
  -- if   1 <- x    // fce=true
  esc = if null esem then
          if fce then
            bool [] (toErrors z "match is exhaustive") ok
          else
            bool (toErrors z "match is non exhaustive")  [] ok
        else
          []

  cses'' = if not fce then cses' else
            cses' ++ [(SNop z, EAny z, SRet z $ EError z (-2))]

-------------------------------------------------------------------------------

stmt envs _   (SCall z exp)  = (ese++esf, ft, fts, SCall z exp') where
                                (ese,ft,fts,exp') = expr z (SUP, (TAny,cz)) envs exp
                                esf = case exp' of
                                  ECall _ _ _ -> []
                                  otherwise  -> (toErrors z "expected call")

stmt envs tpr (SSeq z p1 p2) = (es1++es2, ftMin ft1 ft2, fts1++fts2, SSeq z p1' p2')
  where
    (es1,ft1,fts1,p1') = stmt envs tpr p1
    (es2,ft2,fts2,p2') = stmt envs tpr p2

stmt envs tpr (SLoop z p)    = (es, ft, fts, SLoop z p') where
                                (es,ft,fts,p') = stmt envs tpr p

stmt envs tpr (SRet z exp)   = (es ++ esf, ft, fts, SRet z exp') where
                                (es,ft,fts,exp') = expr z (SUP,tpr) envs exp
                                esf = checkFuncNested "cannot return nested function" exp'

stmt _   _   (SNop z)       = ([], (FuncGlobal,Nothing), [], SNop z)

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

expr :: Ann -> (Relation,TypeC) -> Envs -> Exp -> (Errors, FT_Ups, [FuncType], Exp)
expr z (rel,txp) envs exp = (es1++es2, ft, fts, exp') where
  --(es1, exp') = expr' (rel,bool (TVar False "?" []) txp (rel/=ANY)) envs exp
  --(es1, exp') = expr' (rel,bool (TVar False "?" []) txp (rel==SUP)) envs exp
                           -- only force expected type on SUP
  (es1, ft, fts, exp') = expr' (rel,txp) envs exp
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

expr' :: (Relation,TypeC) -> Envs -> Exp -> (Errors, FT_Ups, [FuncType], Exp)

expr' _       _   (EError  z v)     = ([], (FuncGlobal,Nothing), [], EError  z{typec=(TBot,cz)} v)
expr' _       _   (EUnit   z)       = ([], (FuncGlobal,Nothing), [], EUnit   z{typec=(TUnit,cz)})
expr' (_,txp) _   (EArg    z)       = ([], (FuncGlobal,Nothing), [], EArg    z{typec=txp})

expr' _ envs (EFunc z tpc@(TFunc ft inp out,cs) upv@(EUnit _) p) = (es++esf, ft_ups', closes, EFunc z{typec=tpc'} tpc' upv' p'')
  where
    tpc' = (TFunc ft'' inp out,cs)
    (es,(ft',ups),fts,p') = stmt ([]:envs) (out,cs) p -- add new environment

    ft_ups' = case ups of
                Nothing -> (FuncGlobal, Nothing)
                Just s  -> let s' = (Set.filter (\(_,n) -> n<(length envs - 1))) s in
                            if Set.null s' then
                              (FuncGlobal, Nothing)
                            else
                              (FuncClosure $ Set.size s', Just s')

    -- ft:  how it is defined by the programmer
    -- ft': how it is inferred by its body
    (esf,ft'') = case (ft,ft') of
            (_,_) | ft == ft'             -> ([], ft')
            (FuncGlobal,   FuncGlobal)    -> ([], ft')
            (FuncClosure x,FuncClosure y) -> (es, ft') where
                                              es = if x >= y then [] else
                                                toErrors z "not enough memory : more closures than slots"
            (FuncClosure _,_)             -> (toErrors z "unexpected dimension: function is not a closure", ft')
            --(_,FuncClosure _)           -> (toErrors z "expected `new`: function is a closure", ft')
            (FuncNested, FuncClosure _)   -> ([], FuncNested)
            (FuncUnknown,FuncClosure _)   -> ([], FuncNested)
            (FuncUnknown,_)               -> ([], ft')
            --_ -> error $ show (ft,ft')

    -- (up1,...,upN) = EUps
    p'' = case ft'' of
      FuncClosure _ -> dcls ups' $ SSeq z (attr ups') p' where
                        ups' = map fst $ Set.toAscList $ fromJust ups

                        attr :: [ID_Var] -> Stmt
                        attr [id] = SMatch z True False (EUpv z) [(SNop z,EVar z id,SNop z)]
                        attr ids  = SMatch z True False (EUpv z) [(SNop z,ETuple z $ map (EVar z) ids,SNop z)]

                        dcls :: [ID_Var] -> Stmt -> Stmt
                        dcls ids acc = foldr (\id -> (SVar z id (getTP id))) acc ids

                        getTP :: ID_Var -> TypeC
                        getTP id = case findVars z id envs of
                                            Right [(_, SVar _ _ tpc _)] -> tpc
      otherwise -> p'

    closes = case ft'' of
      FuncClosure _ -> [ft'']
      otherwise     -> []

    upv' = case ft'' of
            FuncClosure _ -> toExp $ map fst $ Set.toAscList $ fromJust ups
            otherwise     -> upv

    toExp :: [ID_Var] -> Exp
    toExp [id] = EVar z id
    toExp ids  = ETuple z $ map (EVar z) ids

expr' _ envs (EMatch z exp pat) = (esp++esem++esc, ftMin ft1 ft2, fts2,
                                  EMatch z{typec=(TData False ["Bool"] [],cz)} exp' pat')
  where
    (esp,ft1,tpp,pat')  = fPat envs False pat
    (ese,ft2,fts2,exp') = expr z (SUP,tpp) envs exp
    (ok, esm)           = (ok, map (toError z) esm) where (ok,esm) = matchX (concat envs) [pat'] exp'
    esem                = bool esm ese (null esm)    -- hide ese if esm
    esc = if null esem then
            bool [] (toErrors z "match is exhaustive") ok
          else
            []

expr' _ envs (EField z hr fld) = (es, (FuncGlobal,Nothing), [], EVar z{typec=(TFunc FuncGlobal inp out,cz)} (hr_str ++ "." ++ fld))
  where
    hr_str = T.hier2str hr

    (inp,out,cz,es) = case find (isData hr_str) (concat envs) of
      Nothing -> (TAny,TAny,cz, toErrors z $ "data '" ++ hr_str ++ "' is not declared")
      Just (SData _ tpc@(TData False _ _) nms (TTuple sts) cz _ _) -> (tpc,out,cz,es) where (out,es) = f nms sts
      Just (SData _ tpc@(TData False _ _) nms st cz _ _)           -> (tpc,out,cz,es) where (out,es) = f nms [st]

    f nms sts = case fld of
      ('_':idx) -> if length sts >= idx' then
                    (sts!!(idx'-1), [])
                   else
                    (TAny,      toErrors z $ "field '" ++ fld ++ "' is not declared")
                   where
                    idx' = read idx
      otherwise -> case (nms, elemIndex fld (fromJust nms)) of
                    (Nothing, _)  -> (TAny, toErrors z $ "field '" ++ fld ++ "' is not declared")
                    (_, Nothing)  -> (TAny, toErrors z $ "field '" ++ fld ++ "' is not declared")
                    (_, Just idx) -> (sts!!idx, [])

expr' (rel,txp) envs (ECons z hr) = (es1++es2, (FuncGlobal,Nothing), [], ECons z{typec=tpc2} hr)
  where
    hr_str = T.hier2str hr
    (tpc1,es1) = case find (isData hr_str) (concat envs) of
      Nothing                       -> ((TBot,cz),
                                        toErrors z $ "data '" ++ hr_str ++ "' is not declared")
      Just (SData _ tdat _ st cs True  _) -> ((f tdat st,cs), toErrors z $ "data '" ++ hr_str ++ "' is abstract")
      Just (SData _ tdat _ st cs False _) -> ((f tdat st,cs), [])

    f tdat TUnit = tdat
    f tdat st    = TFunc FuncGlobal st tdat

    (es2,tpc2) = case relatesC SUP txp tpc1 of
      Left es      -> (map (toError z) es,tpc1)
      Right (tpc,_) -> ([],tpc) where (_,cs)=tpc1

expr' _ envs (ETuple z exps) = (es, ft, fts, ETuple z{typec=(tps',cz)} exps') where
                                rets :: [(Errors,FT_Ups,[FuncType],Exp)]
                                rets  = map (\e -> expr z (SUP,(TAny,cz)) envs e) exps
                                es    = concat $ map fst4 rets
                                exps' = map fou4 rets
                                tps'  = TTuple (map (fst.typec.getAnn) exps')
                                ft    = foldr ftMin (FuncUnknown,Nothing) $ map snd4 rets
                                fts   = concatMap trd4 rets

expr' (rel,txpc@(txp,cxp)) envs (EVar z id@(cid:_)) = (es, ftReq (length envs) (id,ref,n), [], toDer $ EVar z{typec=tpc} id') where    -- EVar x
  (id', tpc, (ref,n), es)
    | (id == "_INPUT") = (id, (TData False ["Int"] [],cz), (False,0), [])
    | otherwise        =
      -- find in top-level envs | id : a
      case findVars z id envs of
        Left  es -> (id, (TAny,cz), (False,0), es)
        Right xs -> case find f xs of
          Nothing -> (id, (TAny,cz), (False,0),
                      map (toError z) $ fromLeft $ relatesC rel txpc (last (map (getTpc.snd) xs)))
                        where getTpc (SVar _ _ tpc _) = tpc
          Just (lnr, SVar _ _  tpc@(_,[])   _) -> (id, tpc, lnr, [])
          Just (lnr, SVar _ _  tpc          _) -> -- generic type
            case find pred (concat envs) of            -- find implementation
              Just (SVar _ k tpc@(tp,cs) _) -> (k, tpc, lnr, [])
              Nothing -> (id, (TAny,cz), lnr, err)
            where
              pred :: Stmt -> Bool
              pred (SVar _ k tpc _) = (dol id `isPrefixOf` k) && (isRight $ relatesC SUP txpc tpc)
              pred _                = False

              err = toErrors z $ "variable '" ++ id ++
                      "' has no associated implementation for '" ++
                      T.show' txp ++ "'"
          where
            f (_, SVar _ _ tpc _) =
              isRight $ relatesC rel txpc (toDer tpc) where
                -- accept ref variables in non-ref context
                toDer tpc = if not (T.isRefableRefC tpc) then tpc else T.toDerC tpc

  toDer exp = if not (T.isRefableRefC tpc) then exp else
                ERefDer z{typec=T.toDerC tpc} exp
              where
                tpc = typec $ getAnn exp

expr' (rel,txpC) envs (ERefRef z exp) = (es, ft, fts, ERefRef z{typec=T.toRefC $ typec $ getAnn exp'} exp')
  where
    (es, ft, fts, exp') = expr z (rel,bool txpC (T.toDerC txpC) (isRefableRefC txpC)) envs exp
    EVar _ id = case exp' of
                  (EVar    _ id)            -> exp'
                  (ERefDer _ e@(EVar _ id)) -> e

expr' (rel,(txp_,cxp)) envs (ECall z f exp) = (bool ese esf (null ese) ++ esa,
                                              ftMin ft1 ft2, fts1++fts2,
                                              ECall z{typec=tpc_out} f' exp')
  where
    (ese, ft1, fts1, exp') = expr z (rel, (TAny,cz)) envs exp
    (esf, ft2, fts2, f')   = expr z (rel, (TFunc FuncUnknown (fst$typec$getAnn$exp') txp_, cxp)) envs f
                                      -- TODO: cs of exp'

    tpc_out = case typec $ getAnn f' of
      (TFunc _ _ out_,cs) -> (out_,cs)
      otherwise           -> (txp_,cxp)

    esa = checkFuncNested "cannot pass nested function" exp'

expr' (_,txp) envs (EAny z) = ([], (FuncGlobal,Nothing), [], EAny z{typec=txp})

--expr' _ _ e = error $ show e
