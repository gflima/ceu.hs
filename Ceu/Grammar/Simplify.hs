module Ceu.Grammar.Simplify where

import Debug.Trace
import Ceu.Grammar.Basic (Stmt(..), Exp(..))

go :: Stmt -> Stmt
go p = stmt p

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (Class z id tp ifc p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Class z id tp ifc p'
  where p' = stmt p

stmt (Inst z cls tp imp p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Inst z cls tp imp p'
  where p' = stmt p

stmt (Data z nms tp abs p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Data z nms tp abs p'
  where p' = stmt p

stmt (Var z id tp p) =
  case p' of
    --Nop z'    -> Nop z'
    _ -> Var z id tp p'
  where p' = stmt p

stmt (Match z b exp cses) = Match z b (expr exp)
                                (map (\(ds,pt,st)->(stmt ds, expr pt, stmt st)) cses)

-- normal form: (Seq x (Seq y (Seq z ...)))
stmt (Seq z1 (Match z2 False exp [(ds,pt,st)]) p) = stmt $ Match z2 False exp [(ds,pt,Seq z1 st p)]
stmt (Seq z1 (Seq z2 p1 p2) p3) = stmt $ Seq z1 p1 (Seq z2 p2 p3)
stmt (Seq z p q) =
  case (p',q') of
    (Nop _,    q')    -> q'
    (p',       Nop _) -> p'
    (Ret z' n, q')    -> Ret z' n
    otherwise         -> Seq z p' q'
  where p' = stmt p
        q' = stmt q

stmt (Loop z p) =
  case p' of
    Ret z' n  -> Ret z' n
    otherwise -> Loop z p'
  where p' = stmt p

stmt (Ret z e) = Ret z (expr e)

stmt p = p

-------------------------------------------------------------------------------

expr :: Exp -> Exp

expr (ECall z e1 e2) = ECall z (expr e1) (expr e2)
expr (EFunc z tp p)  = EFunc z tp (stmt p)
expr e              = e
