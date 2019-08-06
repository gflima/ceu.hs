module Ceu.Grammar.Full.Compile.Func where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Ann               (Ann)
import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Type

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (SClass z cls ctrs ifc) =
  case Cs.toList ctrs of
    [(var,_)]  -> SClass z cls ctrs (stmt $ aux ifc) where
      aux (SSeq  z p1 p2)                  = SSeq  z (aux p1) (aux p2)
      aux (SVar  z id (tp_,ctrs))          = SVar  z id (tp_, Cs.insert (var,cls) ctrs)
      aux (SFunc z id (tp_,ctrs) pars imp) = SFunc z id (tp_, Cs.insert (var,cls) ctrs) pars imp
      aux p                                = p
    otherwise  -> error "TODO: multiple vars"

stmt (SInst  z cls tp@(_,ctrs) imp)    = SInst  z cls tp (stmt $ aux imp)
  where
    aux (SSeq  z p1 p2)                    = SSeq  z (aux p1) (aux p2)
    aux (SVar  z id (tp_',ctrs'))          = SVar  z id (tp_',Cs.union ctrs ctrs')
    aux (SFunc z id (tp_',ctrs') pars imp) = SFunc z id (tp_',Cs.union ctrs ctrs') pars imp
    aux p                                  = p

stmt (SFunc z k tp@(tp_,ctrs) pars imp)    = SSeq z (SVar z k tp) (SSet z True False (EVar z k) (expr $ EFunc z tp pars' imp'))
 where
  (pars',imp') = if ctrs == Cs.cz then (pars,imp) else
                  (map_exp  (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) pars
                  ,map_stmt (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) imp)

stmt (SVar   z id tp)       = SVar   z id tp
stmt (SSet   z ini chk loc exp) = SSet   z ini chk loc (expr exp)
stmt (SMatch z ini chk exp cses)= SMatch z ini chk (expr exp) (map (\(ds,pt,st) -> (stmt ds, expr pt, stmt st)) cses)
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

expr (EFunc  z tpc@(TFunc _ _ inp _,cs) pars imp) = EFunc' z tpc (stmt imp')
  where
    pars' = expr pars
    imp' = tmp $ SSeq z
            (foldr (SSeq z) (SNop z) (toStmts z pars' (inp,cs)))
            (SSeq z
              (SSet z True False pars' (EArg z))
              imp)

    toStmts :: Ann -> Exp -> TypeC -> [Stmt]
    toStmts src loc (tp_,ctrs) = aux src loc tp_
      where
        aux :: Ann -> Exp -> Type -> [Stmt]
        aux z (EAny   _)     _                 = []
        aux z (EUnit  _)     (TUnit False)     = []
        aux z (EVar   _ var) tp_               = [SVar z var (tp_,ctrs)]
        aux z (ETuple _ [])  (TTuple False []) = []
        aux z (ETuple _ [])  _                 = error "arity mismatch"
        aux z (ETuple _ _)   (TTuple False []) = error "arity mismatch"
        aux z (ETuple _ (v1:vs1))
                (TTuple False (v2:vs2))        = (aux z v1 v2) ++ (aux z (ETuple z vs1) (TTuple False vs2))
        aux z (ETuple _ _)  _                  = error "arity mismatch"
        aux z loc           tp                 = error $ show (z,loc,tp)

    tmp p = case pars of
              (EAny _) -> imp
              _        -> p

expr e                      = e
