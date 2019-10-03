module Ceu.Grammar.Simplify where

import Debug.Trace
import Ceu.Grammar.Basic (Stmt(..), Exp(..))

go :: Stmt -> Stmt
go p = stmt p

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (SData z tdat nms flds ctrs abs p) =
  case p' of
    SNop z'   -> SNop z'
    otherwise -> SData z tdat nms flds ctrs abs p'
  where p' = stmt p

stmt (SVar z id tp p) =
  case p' of
    --SNop z'    -> SNop z'
    _ -> SVar z id tp p'
  where p' = stmt p

stmt (SMatch z ini b exp cses) = SMatch z ini b (expr exp)
                                  (map (\(ds,pt,st)->(stmt ds, expr pt, stmt st)) cses)

-- normal form: (SSeq x (SSeq y (SSeq z ...)))
stmt (SSeq z1 (SSeq z2 p1 p2) p3) = stmt $ SSeq z1 p1 (SSeq z2 p2 p3)
stmt (SSeq z p q) =
  case (p',q') of
    (SNop _,    q')    -> q'
    (p',       SNop _) -> p'
    (SRet z' n, q')    -> SRet z' n
    otherwise          -> SSeq z p' q'
  where p' = stmt p
        q' = stmt q

stmt (SLoop z p) =
  case p' of
    SRet z' n -> SRet z' n
    otherwise -> SLoop z p'
  where p' = stmt p

stmt (SRet z e) = SRet z (expr e)

stmt p = p

-------------------------------------------------------------------------------

expr :: Exp -> Exp

expr (ECall z e1 e2)    = ECall z (expr e1) (expr e2)
expr (EFunc z tp upv p) = EFunc z tp (expr upv) (stmt p)
expr e                  = e
