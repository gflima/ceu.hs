module Ceu.Grammar.Simplify where

import Debug.Trace
import Ceu.Grammar.Basic (Stmt(..), Exp(..))

go :: Stmt -> Stmt
go p = stmt p

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (SClass z id tp ifc p) =
  case p' of
    SNop z'   -> SNop z'
    otherwise -> SClass z id tp ifc p'
  where p' = stmt p

stmt (SInst z cls tp imp p) =
  case p' of
    SNop z'   -> SNop z'
    otherwise -> SInst z cls tp imp p'
  where p' = stmt p

stmt (SData z nms tp abs p) =
  case p' of
    SNop z'   -> SNop z'
    otherwise -> SData z nms tp abs p'
  where p' = stmt p

stmt (SVar z id tp p) =
  case p' of
    --SNop z'    -> SNop z'
    _ -> SVar z id tp p'
  where p' = stmt p

stmt (SMatch z b exp cses) = SMatch z b (expr exp)
                                (map (\(ds,pt,st)->(stmt ds, expr pt, stmt st)) cses)

-- normal form: (SSeq x (SSeq y (SSeq z ...)))
stmt (SSeq z1 (SMatch z2 False exp [(ds,pt,st)]) p) = stmt $ SMatch z2 False exp [(ds,pt,SSeq z1 st p)]
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
expr (EFunc z env tp p) = EFunc z env tp (stmt p)
expr e                  = e
