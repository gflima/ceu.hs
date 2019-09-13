module Ceu.Grammar.Full.Compile.Func where

import Debug.Trace
import qualified Data.Map as Map

import Ceu.Grammar.Ann               (Ann)
import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Constraints as Cs
import Ceu.Grammar.Type

import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Match as Match

-------------------------------------------------------------------------------

remSFunc :: Stmt -> Stmt

remSFunc (SFunc z k tp@(tp_,ctrs) par imp) = SVar z k tp (Just $ EFunc z tp par' imp')
  where
    (par',imp') = if ctrs == Cs.cz then (par,imp) else
                    (map_exp  (id2,Prelude.id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) Map.empty par
                    ,map_stmt (id2,Prelude.id,\(tp_,ctrs')->(tp_, Cs.union ctrs ctrs')) Map.empty imp)

remSFunc p = p

-------------------------------------------------------------------------------

remEFuncPar :: Exp -> Exp   -- EFunc -> (SSeq,SSet)

remEFuncPar (EFunc z tpc@(TFunc _ inp _,cs) par imp) = EFunc' z tpc imp'
  where
    imp' = tmp $ (foldr ($) seq (toStmts z par (inp,cs))) where
                  seq = (SSeq z (SSet z True False par (EArg z)) imp)

    toStmts :: Ann -> Exp -> TypeC -> [Stmt->Stmt]
    toStmts src loc (tp_,ctrs) = aux src loc tp_
      where
        aux :: Ann -> Exp -> Type -> [Stmt->Stmt]
        aux z (EAny   _)     _           = []
        aux z (EUnit  _)     TUnit       = []
        aux z (EVar   _ var) tp_         = [SVarS z var (tp_,ctrs) Nothing]
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

remEFuncPar e = e
