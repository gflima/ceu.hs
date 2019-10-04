module Ceu.Grammar.Full.Compile.Func where

import Debug.Trace

import Ceu.Grammar.Ann               (Ann)
import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Type

import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Match as Match

-------------------------------------------------------------------------------

remSFunc :: Stmt -> Stmt

remSFunc (SFunc z k tp@(tp_,cs) par imp) = SVar z k tp (Just $ EFunc z tp par' imp')
  where
    (par',imp') = if cs == Cs.cz then (par,imp) else
                    (map_exp  (id2,Prelude.id,\(tp_,cs')->(tp_, Cs.union cs cs')) [] par
                    ,map_stmt (id2,Prelude.id,\(tp_,cs')->(tp_, Cs.union cs cs')) [] imp)

remSFunc p = p

-------------------------------------------------------------------------------

remEFuncPar :: Exp -> Exp

remEFuncPar (EFunc z tpc@(TFunc _ inp _,cs) par imp) = EFunc' z tpc imp'
  where
    imp' = tmp $ (foldr ($) seq (toStmts z par (inp,cs))) where
                  seq = (SSeq z (SSet z True False par (EArg z)) imp)

    toStmts :: Ann -> Exp -> TypeC -> [Stmt->Stmt]
    toStmts src loc (tp_,cs) = traceShow (loc,tp_) $ aux src loc tp_
      where
        aux :: Ann -> Exp -> Type -> [Stmt->Stmt]
        aux z (EAny   _)     _           = []
        aux z (EUnit  _)     TUnit       = []
        aux z (EVar   _ var) tp_         = [SVarSG z var GNone (tp_,cs) Nothing]
        aux z (ETuple _ [])  (TTuple []) = []
        aux z (ETuple _ [])  _           = error "arity mismatch"
        aux z (ETuple _ _)   (TTuple []) = error "arity mismatch"
        aux z (ETuple _ (v1:vs1))
                (TTuple (v2:vs2))        = (aux z v1 v2) ++ (aux z (ETuple z vs1) (TTuple vs2))
        aux z (ETuple _ _)  _            = error "arity mismatch"
        --aux z loc           tp           = error $ show (loc,tp)

    tmp p = case par of
              (EAny _) -> imp
              _        -> p

remEFuncPar e = e
