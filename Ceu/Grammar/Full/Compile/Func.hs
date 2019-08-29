module Ceu.Grammar.Full.Compile.Func where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Ann               (Ann)
import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Type

compile :: Stmt -> Stmt
compile p = map_stmt (stmt,expr,id) $ map_stmt (remSFunc,id,id) p where

-------------------------------------------------------------------------------

remSFunc :: Stmt -> Stmt

remSFunc (SFunc z k tp@(tp_,ctrs) par imp) = SSeq z (SVar z k tp)
                                                    (SSet z True False (EVar z k) (EFunc z tp par' imp'))
  where
    (par',imp') = if ctrs == Cs.cz then (par,imp) else
                    (map_exp  (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) par
                    ,map_stmt (id,id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) imp)

remSFunc p = p

-------------------------------------------------------------------------------

stmt :: Stmt -> Stmt

stmt (SClass z cls ctrs ifc) =
  case Cs.toList ctrs of
    [(var,_)]  -> SClass z cls ctrs (aux ifc) where
      aux (SSeq  z p1 p2)                 = SSeq  z (aux p1) (aux p2)
      aux (SVar  z id (tp_,ctrs))         = SVar  z id (tp_, Cs.insert (var,cls) ctrs)
      aux (SFunc z id (tp_,ctrs) par imp) = SFunc z id (tp_, Cs.insert (var,cls) ctrs) par imp
      aux p                               = p
    otherwise  -> error "TODO: multiple vars"

stmt (SInst  z cls tp@(_,ctrs) imp)    = SInst  z cls tp (aux imp)
  where
    aux (SSeq  z p1 p2)                   = SSeq  z (aux p1) (aux p2)
    aux (SVar  z id (tp_',ctrs'))         = SVar  z id (tp_',Cs.union ctrs ctrs')
    aux (SFunc z id (tp_',ctrs') par imp) = SFunc z id (tp_',Cs.union ctrs ctrs') par imp
    aux p                                 = p

stmt p = p

-------------------------------------------------------------------------------

expr :: Exp -> Exp

expr (EFunc  z tpc@(TFunc _ inp _,cs) par imp) = EFunc' z tpc imp'
  where
    imp' = tmp $ SSeq z
            (foldr (SSeq z) (SNop z) (toStmts z par (inp,cs)))
            (SSeq z
              (SSet z True False par (EArg z))
              imp)

    toStmts :: Ann -> Exp -> TypeC -> [Stmt]
    toStmts src loc (tp_,ctrs) = aux src loc tp_
      where
        aux :: Ann -> Exp -> Type -> [Stmt]
        aux z (EAny   _)     _           = []
        aux z (EUnit  _)     TUnit       = []
        aux z (EVar   _ var) tp_         = [SVar z var (tp_,ctrs)]
        aux z (ETuple _ [])  (TTuple []) = []
        aux z (ETuple _ [])  _           = error "arity mismatch"
        aux z (ETuple _ _)   (TTuple []) = error "arity mismatch"
        aux z (ETuple _ (v1:vs1))
                (TTuple (v2:vs2))        = (aux z v1 v2) ++ (aux z (ETuple z vs1) (TTuple vs2))
        aux z (ETuple _ _)  _            = error "arity mismatch"
        aux z loc           tp           = error $ show (z,loc,tp)

    tmp p = case par of
              (EAny _) -> imp
              _        -> p

expr e = e
