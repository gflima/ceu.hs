module Ceu.Grammar.Full.Compile.Func where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import qualified Ceu.Grammar.Type        as T

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (SClass z cls ctrs ifc) =
  case Cs.toList ctrs of
    [(var,_)]  -> SClass z cls ctrs (stmt $ aux ifc) where
      aux (SSeq  z p1 p2)             = SSeq  z (aux p1) (aux p2)
      aux (SVar  z id (tp_,ctrs))     = SVar  z id (tp_, Cs.insert (var,cls) ctrs)
      aux (SFunc z id (tp_,ctrs) imp) = SFunc z id (tp_, Cs.insert (var,cls) ctrs) imp
      aux p                           = p
    otherwise  -> error "TODO: multiple vars"

stmt (SInst  z cls tp@(_,ctrs) imp)    = SInst  z cls tp (stmt $ aux imp)
  where
    aux (SSeq  z p1 p2)               = SSeq  z (aux p1) (aux p2)
    aux (SVar  z id (tp_',ctrs'))     = SVar  z id (tp_',Cs.union ctrs ctrs')
    aux (SFunc z id (tp_',ctrs') imp) = SFunc z id (tp_',Cs.union ctrs ctrs') imp
    aux p                             = p

stmt (SFunc z k tp@(tp_,ctrs) imp)    = SSeq z (SVar z k tp) (SSet z False (EVar z k) (EFunc z tp (stmt imp')))
 where
  imp' = if ctrs == Cs.cz then imp else
          map_stmt (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) imp

stmt (SVar   z id tp)       = SVar   z id tp
stmt (SSet   z chk loc exp) = SSet   z chk loc (expr exp)
stmt (SMatch z chk exp cses)= SMatch z chk (expr exp) (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses)
stmt (SCall z exp)          = SCall z (expr exp)
stmt (SIf    z exp p1 p2)   = SIf    z (expr exp) (stmt p1) (stmt p2)
stmt (SSeq   z p1 p2)       = SSeq   z (stmt p1) (stmt p2)
stmt (SLoop  z p)           = SLoop  z (stmt p)
stmt (SScope z p)           = SScope z (stmt p)
stmt (SRet   z exp)         = SRet   z (expr exp)
stmt p                      = p

expr :: Exp -> Exp
expr (ETuple z es)          = ETuple z (map expr es)
expr (ECall  z e1 e2)       = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)        = EFunc  z tp (stmt p)
expr e                      = e
