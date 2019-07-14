module Ceu.Grammar.Match where

import Data.Bool (bool)
import Data.List (find, unzip, unzip3, isPrefixOf)

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann
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

matchX :: Ann -> Bool -> [Exp] -> Exp -> (Bool, Errors)
matchX z fce pats exp = matchX' z fce pats [Left exp] where
  matchX' :: Ann -> Bool -> [Exp] -> [Either Exp TypeC] -> (Bool, Errors)
  matchX' _ _   [] [] = (False, [])   -- OK
  matchX' _ _   _  [] = (False, [])   -- reduntant
  matchX' _ _   [] _  = (True,  [])   -- non-exhaustive
  matchX' z fce (pat:pats) (exp:exps) = (ret, es'++es) where
    (exps',es') = case exp of
                    Left  x -> matchE z pat x
                    Right x -> matchT pat x
    (ret,es) = matchX' z fce pats (exps'++exps)

{-
  matchX' _ _ es pats (exp:exps) = (and l1, concat l2) where
                                  (l1,l2) = unzip $ map (flip (match z) exp) pats
-}

-------------------------------------------------------------------------------

matchE :: Ann -> Exp -> Exp -> ([Either Exp TypeC], Errors)

matchE _ _                 (EArg   _)         = ([], [])

-- structural match
matchE _ (EUnit _)         (EUnit  _)         = ([], [])
matchE z (ECons _ hr1)     (ECons  _ hr2)     = ([], es) where
                                                es = if hr1 `isPrefixOf` hr2 then [] else
                                                      [toError z $ "match never succeeds : data mismatch"]
matchE z (ECall _ el1 er1) exp@(ECall  _ el2 er2) = ([] {-may1||may2-}, es1++es2) where
                                                      (exps1, es1) = matchE z el1 el2
                                                      (exps2, es2) = matchE z er1 er2
matchE z (ETuple z1 els)   exp@(ETuple z2 ers)    = ([] {-or mays-}, concat eses ++ es) where
                                                      es = if lenl == lene then [] else
                                                        [toError z $ "match never succeeds : arity mismatch"]
                                                      (exps, eses) = unzip $ zipWith (matchE z) els' ers' where
                                                        els' = els ++ replicate (lene - lenl) (EAny z1)
                                                        ers' = ers ++ replicate (lenl - lene) (EError z2 (-2))
                                                      lenl  = length els
                                                      lene  = length ers

-- structural fail
matchE z l e | (isE l && isE e) = ([], [toError z $ "match never succeeds"]) where
  isE (EUnit  _)              = True
  isE (ETuple _ _)            = True
  isE (ECons  _ _)            = True
  isE (ECall _ (ECons _ _) _) = True
  isE _                       = False

-- contravariant on constants (SUB)
matchE _ (EUnit  z)      exp            = ([Left exp], es) where
                                          es = (relatesErrors SUB (TUnit,cz) (type_ $ getAnn exp))

-- non-constants: LAny,LVar (no fail) // LExp (may fail)
matchE _ (EVar _ _)      _              = ([],    [])
matchE _ (EAny _)        _              = ([],    [])
matchE _ (EExp _ _)      exp            = ([Left exp], [])

-- rec
matchE _ loc             exp            = matchT loc (type_ $ getAnn exp) where

-------------------------------------------------------------------------------

matchT :: Exp -> TypeC -> ([Either Exp TypeC], Errors)

matchT (EUnit _)       tp = ([], es) where
                              es = [] --map (toError z) (relatesErrors SUB (TUnit,cz) tp)
matchT (EVar  _ _)     _  = ([], [])
matchT (EAny  _)       _  = ([], [])
matchT (EExp  _ _)     _  = ([] {-True-},  [])
matchT (ECons _ hr1)   tp = case tp of
                              (TData hr2 _ st, ctrs) -> (bool [] [Right tp] may, []) where
                                                          may = (hr2 `isPrefixOf` hr1) && (hr1 /= hr2)
                              otherwise              -> ([], [])
matchT (ETuple _ ls)   tp = case tp of
                              (TTuple tps, ctrs)     -> (bool [Right tp] [] (all null tps'), concat ess) where
                                                          (tps', ess) = unzip $ zipWith matchT ls (map f tps)
                                                          f tp = (tp,ctrs)
                              otherwise              -> ([], [])
matchT (ECall _ el er) tp = case tp of
                              (TData h ofs st, ctrs) -> (bool [Right tp] [] (null may1 && null may2), es1 ++ es2) where
                                                          (may1, es1) = matchT el tp
                                                          (may2, es2) = matchT er (st,ctrs)
                              otherwise              -> ([], [])
