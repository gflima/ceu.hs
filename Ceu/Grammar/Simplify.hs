module Ceu.Grammar.Simplify where

import Debug.Trace
import Ceu.Grammar.Basic (Stmt(..), Exp(..))

go :: Stmt -> Stmt
go p = stmt p

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (Class z me ext ifc p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Class z me ext ifc p'
  where p' = stmt p

stmt (Inst z me imp p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Inst z me imp p'
  where p' = stmt p

stmt (Data z id vars flds abs p) =
  case p' of
    Nop z'    -> Nop z'
    otherwise -> Data z id vars flds abs p'
  where p' = stmt p

stmt (Var z id gen tp p) =
  case p' of
    --Nop z'    -> Nop z'
    _ -> Var z id gen tp p'
  where p' = stmt p

-- TODO: loc may contain exp which may contain stmt
stmt (Match z b loc exp p q) = Match z b loc (expr exp) (stmt p) (stmt q)

-- normal form: (Seq x (Seq y (Seq z ...)))
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

expr (Call z e1 e2) = Call z (expr e1) (expr e2)
expr (Func z tp p)  = Func z tp (stmt p)
expr e              = e
