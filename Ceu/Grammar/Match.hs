module Ceu.Grammar.Match where

import Data.Bool (bool)
import Data.List (find, unzip, unzip3, isPrefixOf)

import Ceu.Trace
import Ceu.Grammar.Ann                (getAnn, type_, toError)
import Ceu.Grammar.Globals
import Ceu.Grammar.Basic
import Ceu.Grammar.Constraints as Cs  (Pair, cz, toList, hasClass)
import Ceu.Grammar.Type        as T   (Type(..), TypeC, hier2str,
                                       Relation(..), relatesErrors)

-------------------------------------------------------------------------------

-- Match must be covariant on variables and contravariant on constants:
--  LVar    a     <- x      # assign # a     SUP x
--  LExp    a     <- x      # match  # a     SUP x
--  LAny          <- x      # match  # BOT   SUB x
--  LUnit         <- x      # match  # unit  SUB x
--  LCons   a b   <- ECons x # match  # a     SUP ECons x | b match x
--  LCons   a.* b <- x      # match  # a     SUP x      | b match x
--  LTuple  (a,b) <- (x,y)  # match  # (B,B) SUB (x,y)  | a match x,  b match y
--  LTuple  (a,b) <- x      # match  # (B,B) SUB x      | a match x1, b match x2

matchX :: [Stmt] -> [Exp] -> Exp -> (Bool, Errors)
matchX ids pats exp = matchX' ids pats [Left exp] where
  matchX' :: [Stmt] -> [Exp] -> [Either Exp TypeC] -> (Bool, Errors)
  matchX' _ [] [] = (False, [])   -- OK
  matchX' _ l  [] = (False, map (\pat -> toError (getAnn pat) "pattern is redundant") l)
  matchX' _ [] _  = (True,  [])   -- non-exhaustive
  matchX' ids (pat:pats) (exp:exps) = (ret, es'++es) where
    (exps',es') = case exp of
                    Left  x -> matchE ids pat x
                    Right x -> matchT ids pat x
    (ret,es) = matchX' ids pats (exps'++exps)

{-
  matchX' _ _ es pats (exp:exps) = (and l1, concat l2) where
                                  (l1,l2) = unzip $ map (flip (match z) exp) pats
-}

-------------------------------------------------------------------------------

matchE :: [Stmt] -> Exp -> Exp -> ([Either Exp TypeC], Errors)

matchE _ _                 (EArg   _)         = ([], [])

-- structural match
matchE _ (EUnit _)         (EUnit  _)         = ([], [])
matchE _ (ECons z hr1)     exp@(ECons  _ hr2) = if hr1 `isPrefixOf` hr2 then ([],[]) else
                                                  ([Left exp], [toError z $ "match never succeeds : data mismatch"])
matchE ids (ECall _ el1 er1) exp@(ECall  _ el2 er2) = ([] {-may1||may2-}, es1++es2) where
                                                        (exps1, es1) = matchE ids el1 el2
                                                        (exps2, es2) = matchE ids er1 er2
matchE ids (ETuple z1 els)   exp@(ETuple z2 ers)    = (ret {-or mays-}, concat eses ++ es) where
                                                        (ret,es) = if lenl == lene then ([],[]) else
                                                                    ([Left exp], [toError z1 $ "match never succeeds : arity mismatch"])
                                                        (exps, eses) = unzip $ zipWith (matchE ids) els' ers' where
                                                          els' = els ++ replicate (lene - lenl) (EAny z1)
                                                          ers' = ers ++ replicate (lenl - lene) (EError z2 (-2))
                                                        lenl  = length els
                                                        lene  = length ers

-- structural fail
matchE _ l e | (isE l && isE e) = ([Left e], [toError (getAnn l) $ "match never succeeds"]) where
  isE (EUnit  _)              = True
  isE (ETuple _ _)            = True
  isE (ECons  _ _)            = True
  isE (ECall _ (ECons _ _) _) = True
  isE _                       = False

-- contravariant on constants (SUB)
matchE _ (EUnit  z)      exp    = ([Left exp], es) where
                                    es = (relatesErrors SUB (TUnit,cz) (type_ $ getAnn exp))

-- non-constants: LAny,LVar (no fail) // LExp (may fail)
matchE _ (EVar _ _)      _      = ([],    [])
matchE _ (EAny _)        _      = ([],    [])
matchE _ (EExp _ _)      exp    = ([Left exp], [])

-- rec
matchE ids loc           exp    = matchT ids loc (type_ $ getAnn exp) where

-------------------------------------------------------------------------------

matchT :: [Stmt] -> Exp -> TypeC -> ([Either Exp TypeC], Errors)

matchT _   (EUnit _)       tp = ([], [])
matchT _   (EVar  _ _)     _  = ([], [])
matchT _   (EAny  _)       _  = ([], [])
matchT _   (EExp  _ _)     tp = ([Right tp], [])
matchT ids (ECons z hr1)   tp = case tp of
                                  (TData hr2 _ st, ctrs) -> if hr1 `isPrefixOf` hr2 then ([],[]) else
                                                              if hr2 `isPrefixOf` hr1 then
                                                                traceShow subs([Right tp],[])
                                                              else
                                                                ([Right tp], [toError z $ "match never succeeds : data mismatch"])
                                    where
                                      subs = map f $ filter pred ids where
                                              pred (Data  _ (TData hr2 _ _,_) _ _) = gt hr1 hr2
                                              pred _ = False
                                              f (Data  _ (TData hr2 _ _,_) _ _) = hr2
                                      gt sup sub = (sup `isPrefixOf` sub) && (length sup < length sub)
                                  otherwise              -> ([], [])
matchT ids (ETuple _ ls)   tp = case tp of
                                  (TTuple tps, ctrs)     -> (bool [Right tp] [] (all null tps'), concat ess) where
                                                              (tps', ess) = unzip $ zipWith (matchT ids) ls (map f tps)
                                                              f tp = (tp,ctrs)
                                  otherwise              -> ([], [])
matchT ids (ECall _ el er) tp = case tp of
                                  (TData h ofs st, ctrs) -> (bool [Right tp] [] (null may1 && null may2), es1 ++ es2) where
                                                              (may1, es1) = matchT ids el tp
                                                              (may2, es2) = matchT ids er (st,ctrs)
                                  otherwise              -> ([], [])
