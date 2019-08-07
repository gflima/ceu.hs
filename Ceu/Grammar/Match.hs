module Ceu.Grammar.Match where

import Data.Bool (bool)
import Data.List (find, unzip, unzip3, isPrefixOf)

import Ceu.Trace
import Ceu.Grammar.Ann                (getAnn, typec, toError)
import Ceu.Grammar.Globals
import Ceu.Grammar.Basic
import Ceu.Grammar.Constraints as Cs  (Pair, cz, toList, hasClass)
import Ceu.Grammar.Type        as T   (Type(..), TypeC, hier2str,
                                       Relation(..), relatesErrorsC)

-------------------------------------------------------------------------------

subs :: [Stmt] -> ID_Data_Hier -> [ID_Data_Hier]
subs envs hr = g $ ints ++ (map f $ filter pred envs) where
  ints = if hr == ["Int"] then
          [["Int","?"]]
         else if take 1 hr == ["Int"] then
          [hr]
         else
          []
          -- Int that will never match any numeric pattern

  pred (SData  _ _ (TData False hrD _ _,_) False _) = gt hr hrD
          -- ignore abstract data
  pred _ = False

  f (SData  _ _ (TData False hrD _ _,_) _ _) = hrD

  gt sup sub = (sup `isPrefixOf` sub) -- && (length sup < length sub)

  g l = bool l [hr] (null l)  -- prevents empty return in case of abstract data only (prevents bad error messages)

-------------------------------------------------------------------------------

-- SMatch must be covariant on variables and contravariant on constants:
--  LVar    a     <- x      # assign # a     SUP x
--  LExp    a     <- x      # match  # a     SUP x
--  LAny          <- x      # match  # BOT   SUB x
--  LUnit         <- x      # match  # unit  SUB x
--  LCons   a b   <- ECons x # match  # a     SUP ECons x | b match x
--  LCons   a.* b <- x      # match  # a     SUP x      | b match x
--  LTuple  (a,b) <- (x,y)  # match  # (B,B) SUB (x,y)  | a match x,  b match y
--  LTuple  (a,b) <- x      # match  # (B,B) SUB x      | a match x1, b match x2

matchX :: [Stmt] -> [Exp] -> Exp -> (Bool, Errors)
matchX envs pats exp = matchX' envs pats (expandE envs exp) where
  matchX' :: [Stmt] -> [Exp] -> [Exp] -> (Bool, Errors)
  matchX' _ [] [] = (True,  [])   -- OK
  matchX' _ l  [] = (True,  map (\pat -> toError (getAnn pat) "pattern is redundant") l)
  matchX' _ [] _  = (False, [])   -- non-exhaustive

  matchX' envs (pat:pats) exps = (ret, es'++es) where
    (exps',es') = foldr f ([],[]) exps

    f :: Exp -> ([Exp],Errors) -> ([Exp],Errors)
    f exp (exps,es) = case matchE pat exp of
                        (True, es') -> (exps,     es'++es)
                        (False,es') -> (exp:exps, es'++es)

    (ret,es) = matchX' envs pats exps'

-------------------------------------------------------------------------------

expandE :: [Stmt] -> Exp -> [Exp]

expandE envs (ECons z hrE)   = foldr f [] (subs envs hrE) where
                                f hr exps = (ECons z hr) : exps

expandE envs (ECall z e1 e2) = foldr f [] (combos [expandE envs e1, expandE envs e2]) where
                                f :: [Exp] -> [Exp] -> [Exp]
                                f [e1,e2] exps = (ECall z e1 e2) : exps

expandE envs (ETuple z l)    = foldr f [] (combos $ map (expandE envs) l) where
                                f l' exps = (ETuple z l') : exps

expandE envs e@(EVar z id)   = foldr f [] (expandT envs tp) where
                                f tp' exps = (EVar z{typec=(tp',ctrs)} id) : exps
                                (tp,ctrs) = typec $ getAnn e

expandE _ e = [e]

-------------------------------------------------------------------------------

expandT :: [Stmt] -> Type -> [Type]

expandT envs (TData False hrT ofs st) = foldr f [] (subs envs hrT) where
                                          f hr tps = (TData False hr ofs st) : tps

expandT envs (TTuple False l)         = foldr f [] (combos $ map (expandT envs) l) where
                                          f l' tps = (TTuple False l') : tps

expandT _    tp                       = [tp]

-------------------------------------------------------------------------------

matchE :: Exp -> Exp -> (Bool, Errors)

matchE _                 (EArg   _)         = (True, [])

-- structural match
matchE (EUnit _)         (EUnit  _)         = (True, [])
matchE (ECons z hrP)     (ECons  _ hrE)     = if hrP `isPrefixOf` hrE then (True,[]) else
                                                (False, [toError z $ "match never succeeds : data mismatch"])
matchE (ECall _ el1 er1) (ECall  _ el2 er2) = (ok1 && ok2, es1++es2) where
                                                (ok1, es1) = matchE el1 el2
                                                (ok2, es2) = matchE er1 er2
matchE (ETuple z1 els)   (ETuple z2 ers)    = (ok && and oks, concat eses ++ es) where
                                                (ok,es) = if lenl == lene then (True,[]) else
                                                            (False, [toError z1 $ "match never succeeds : arity mismatch"])
                                                (oks, eses) = unzip $ zipWith matchE els' ers' where
                                                  els' = els ++ replicate (lene - lenl) (EAny z1)
                                                  ers' = ers ++ replicate (lenl - lene) (EError z2 (-2))
                                                lenl  = length els
                                                lene  = length ers

-- structural fail
matchE l e | (isE l && isE e) = (False, [toError (getAnn l) $ "match never succeeds"]) where
  isE (EUnit  _)              = True
  isE (ETuple _ _)            = True
  isE (ECons  _ _)            = True
  isE (ECall _ (ECons _ _) _) = True
  isE _                       = False

-- contravariant on constants (SUB)
matchE (EUnit  z)      exp    = (False, es) where
                                  es = (relatesErrorsC SUB (TUnit False,cz) (typec $ getAnn exp))

-- non-constants: LAny,LVar (no fail) // LExp (may fail)
matchE (EVar _ _)      _      = (True,  [])
matchE (EAny _)        _      = (True,  [])
matchE (EExp _ _)      exp    = (False, [])

-- rec
matchE loc             exp    = matchT loc (typec $ getAnn exp)

-------------------------------------------------------------------------------

matchT :: Exp -> TypeC -> (Bool, Errors)

matchT (EUnit _)       tp = (True,  [])
matchT (EVar  _ _)     _  = (True,  [])
matchT (EAny  _)       _  = (True,  [])
matchT (EExp  _ _)     tp = (False, [])

matchT (ERefDer _ e)   tp = matchT e tp
matchT (ERefIni _ e)   tp = matchT e tp

matchT (ECons z hrP)   tp =
  case tp of
    (TData False hrE ofs st, ctrs) -> if hrP `isPrefixOf` hrE then (True,[]) else
                                        if take 1 hrE `isPrefixOf` take 1 hrP then
                                          (False, [])
                                        else
                                          (False, [toError z $ "match never succeeds : data mismatch"])
    otherwise                      -> (True, [])

matchT (ETuple _ ls)   tp =
  case tp of
    (TTuple False tps, ctrs)       -> (and oks, concat ess) where
                                        (oks, ess) = unzip $ zipWith matchT ls (map f tps)
                                        f tp = (tp,ctrs)
    otherwise                      -> (True, [])

matchT (ECall _ el er) tp =
  case tp of
    (TData False h ofs st, ctrs)   -> (ok1 && ok2, es1 ++ es2) where
                                        (ok1, es1) = matchT el tp
                                        (ok2, es2) = matchT er (st,ctrs)
    otherwise                      -> (True, [])