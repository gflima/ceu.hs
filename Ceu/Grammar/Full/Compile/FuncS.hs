module Ceu.Grammar.Full.Compile.FuncS where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import qualified Ceu.Grammar.Type        as T

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Class z cls ctrs ifc) =
  case Cs.toList ctrs of
    [(var,_)]  -> Class z cls ctrs (stmt $ aux ifc) where
      aux (Seq   z p1 p2)              = Seq   z (aux p1) (aux p2)
      aux (Var   z id (tp_,ctrs))      = Var   z id (tp_, Cs.insert (var,cls) ctrs)
      aux (FuncS z id (tp_,ctrs) imp)  = FuncS z id (tp_, Cs.insert (var,cls) ctrs) imp
      aux p                            = p
    otherwise  -> error "TODO: multiple vars"

stmt (Inst  z cls tp@(_,ctrs) imp)    = Inst  z cls tp (stmt $ aux imp)
  where
    aux (Seq   z p1 p2)               = Seq   z (aux p1) (aux p2)
    aux (Var   z id (tp_',ctrs'))     = Var   z id (tp_',Cs.union ctrs ctrs')
    aux (FuncS z id (tp_',ctrs') imp) = FuncS z id (tp_',Cs.union ctrs ctrs') imp
    aux p                             = p

stmt (FuncS z k tp@(tp_,ctrs) imp) = Seq z (Var z k tp) (Set z False (EVar z k) (EFunc z tp (stmt imp')))
 where
  imp' = if ctrs == Cs.cz then imp else
          map_stmt (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) imp

stmt (Var   z id tp)       = Var   z id tp
stmt (Set   z chk loc exp) = Set   z chk loc (expr exp)
stmt (Match z exp cses)    = Match z (expr exp) (map (\(pt,st) -> (expr pt, stmt st)) cses)
stmt (CallS z exp)         = CallS z (expr exp)
stmt (If    z exp p1 p2)   = If    z (expr exp) (stmt p1) (stmt p2)
stmt (Seq   z p1 p2)       = Seq   z (stmt p1) (stmt p2)
stmt (Loop  z p)           = Loop  z (stmt p)
stmt (Scope z p)           = Scope z (stmt p)
stmt (Ret   z exp)         = Ret   z (expr exp)
stmt p                     = p

expr :: Exp -> Exp
expr (ETuple z es)         = ETuple z (map expr es)
expr (ECall  z e1 e2)      = ECall  z (expr e1) (expr e2)
expr (EFunc  z tp p)       = EFunc  z tp (stmt p)
expr e                     = e
