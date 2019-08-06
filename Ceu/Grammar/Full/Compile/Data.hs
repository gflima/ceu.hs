module Ceu.Grammar.Full.Compile.Data where

import Debug.Trace
import Data.List (find)
import Data.Bool (bool)

import Ceu.Grammar.Ann
import Ceu.Grammar.Globals
import Ceu.Grammar.Type               (Type(..),TypeC,instantiate,getSuper,hier2str,FuncType(..))
import Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = stmt [] p

-- Instantiates variable declarations of TData with their complete types:
--
-- data Pair with (Int,Int)
--    var p : Pair
-- becomes
--    var p : Pair (Int,Int)
--
-- data Pair with (a,b,Bool)
--    var p : Pair of (X,Y)
-- becomes
--    var p : Pair (X,Y,Bool)

-------------------------------------------------------------------------------

stmt :: [Stmt] -> Stmt -> Stmt
stmt ds (SClass'' z id  cs ifc p) = SClass'' z id  cs ifc (stmt ds p)
stmt ds (SInst''  z cls tp imp p) = SInst''  z cls tp imp (stmt ds p)
stmt ds (SData''  z nms tp abs p) = SData''  z nms' tp' abs (stmt (d':ds) (faccs z nms' tp' p))
                                    where
                                      (nms',tp') = fdata ds nms tp
                                      d'         = SData'' z nms' tp' abs p
stmt ds (SVar''   z var tp p)     = SVar''   z var (fvar ds tp) (stmt ds p)
stmt ds (SMatch'  z ini chk exp cses) = SMatch' z ini chk (expr ds exp)
                                          (map (\(xs,pt,st) -> (stmt ds xs, expr ds pt, stmt ds st)) cses)
stmt ds (SCall    z exp)          = SCall    z (expr ds exp)
stmt ds (SSeq     z p1 p2)        = SSeq     z (stmt ds p1) (stmt ds p2)
stmt ds (SLoop    z p)            = SLoop    z (stmt ds p)
stmt ds (SRet     z exp)          = SRet     z (expr ds exp)
stmt _  p                         = p

-------------------------------------------------------------------------------

expr :: [Stmt] -> Exp -> Exp
expr ds (ETuple z es)            = ETuple z (map (expr ds) es)
expr ds (ECall  z e1 e2)         = ECall  z (expr ds e1) (expr ds e2)
expr ds (EFunc' z tp imp)        = EFunc' z tp (stmt ds imp)
expr _  e                        = e

-------------------------------------------------------------------------------

fdata :: [Stmt] -> Maybe [String] -> TypeC -> (Maybe [String], TypeC)
fdata ds nms tp@(TData False id ofs st, ctrs) = case getSuper id of
  Nothing  -> (nms,tp)
  Just sup -> case find (\(SData'' _ _ (TData False id' _ _,_) _ _) -> id'==sup) ds of
                Nothing -> (nms,tp)
                Just (SData'' _ nms' (TData False _ ofs' st',ctrs') _ _) ->
                  case any (\v2 -> elem v2 ofs) ofs' of
                    True  -> error $ "TODO: repeated variables"
                    False -> (ret, (TData False id (ofs' ++ ofs) (cat st' st), Cs.union ctrs' ctrs))
                             where
                              ret = case (nms',nms) of
                                      (Nothing,Nothing) -> Nothing
                                      (Just l, Nothing) -> error "TODO"
                                      (Nothing,Just l)  -> error "TODO"
                                      (Just l1,Just l2) -> Just $ l1 ++ l2
  where
    cat :: Type -> Type -> Type
    cat (TUnit False)     tp                = tp
    cat tp                (TUnit False)     = tp
    cat (TTuple False l1) (TTuple False l2) = TTuple False $ l1 ++ l2
    cat (TTuple False l1) tp                = TTuple False $ l1 ++ [tp]
    cat tp                (TTuple False l2) = TTuple False $ tp :  l2
    cat tp1               tp2               = TTuple False $ [tp1,tp2]

-------------------------------------------------------------------------------

fvar :: [Stmt] -> TypeC -> TypeC
fvar ds (tp_,ctrs) = (fvar' ds tp_, ctrs)
  where
    fvar' :: [Stmt] -> Type -> Type
    fvar' ds (TData False hier ofs st) = TData False hier ofs $
      case find (\(SData'' _ _ (TData False h' _ _,_) _ _) -> h'==hier) ds of
        Nothing -> fvar' ds st
        Just (SData'' _ _ (TData False _ ofs' st',_) _ _)
                -> instantiate (zip (map (\(TAny False v)->v) ofs') ofs) st'
    fvar' ds (TFunc False ftp inp out) = TFunc False ftp (fvar' ds inp) (fvar' ds out)
    fvar' ds (TTuple False tps)    = TTuple False $ map (fvar' ds) tps
    fvar' _  tp                    = tp

-------------------------------------------------------------------------------

-- accessors
-- data X with (...,Int,...)
-- X_2 : (X -> Int)

faccs :: Ann -> Maybe [ID_Var] -> TypeC -> Stmt -> Stmt
faccs z nms (tpD@(TData False hr _ st),cz) p = accs where
  (accs,_) = foldr f (p, 1) (g st)

  hr_str = hier2str hr

  g :: Type -> [Type]
  g (TTuple False l) = l
  g (TUnit False)    = []
  g tp               = [tp]

  f :: Type -> (Stmt,Int) -> (Stmt,Int)
  f tp (p,idx) = (SVar'' z id (TFunc False FuncGlobal tpD tp,cz)
                    (SMatch' z True False body [(SNop z, EVar z id, nm p)])
                 ,idx+1)
                 where
                  id = hr_str ++ "._" ++ show idx

                  body = EFunc' z (TFunc False FuncGlobal tpD tp,cz)
                          (SVar'' z "ret" (tp,cz)
                            (SMatch' z True False (EArg z) [(SNop z, ret, SRet z (EVar z "ret"))]))
                  ret  = ECall z (ECons z hr) (bool (ETuple z repl) (repl!!0) (len st == 1))
                  repl = take (idx-1) anys ++ [EVar z "ret"] ++ drop idx anys
                  anys = replicate (len st) (EAny z)

                  len (TTuple False l) = length l
                  len _          = 1

                  nm p = case nms of
                          Nothing -> p
                          Just l  -> SVar'' z idm (TFunc False FuncGlobal tpD tp,cz)
                                      (SMatch' z True False body [(SNop z, EVar z idm, p)])
                                     where
                                      idm = hr_str ++ "." ++ (l!!(idx-1))
                                      body = EFunc' z (TFunc False FuncGlobal tpD tp,cz)
                                              (SRet z (ECall z (EVar z id) (EArg z)))
