module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, getAnn)
import Ceu.Grammar.Type     (Type(..))
import qualified Ceu.Grammar.Basic   as B
import qualified Ceu.Grammar.TypeSys as T
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Seq   as Seq

prelude :: Ann -> Stmt -> Stmt
prelude z p =
    (Seq z (Data z "Int"  [] [] False)
    (Seq z (Data z "Bool" [] [] False)
    (Seq z (Var  z "negate" (TypeF (Type1 "Int")                      (Type1 "Int")))
    (Seq z (Var  z "=="     (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Bool")))
    (Seq z (Var  z "+"      (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")))
    (Seq z (Var  z "-"      (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")))
    (Seq z (Var  z "/"      (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")))
    (Seq z (Var  z "*"      (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")))
           p))))))))

compile :: Stmt -> (Errors, Stmt)
compile p = --traceShowId $ 
    comb Scope.compile    $
    comb Seq.compile      $
      ([], p)
  where
    comb :: (Stmt -> (Errors,Stmt)) -> (Errors,Stmt) -> (Errors,Stmt)
    comb f (es,p) = (es++es',p') where (es',p') = f p

compile' :: Stmt -> (Errors, B.Stmt)
compile' p = (es1++es2++es3, p3)
  where
    (es1,p1) = compile p
    (es2,p2) = toBasic p1
    (es3,p3) = T.go p2

go :: Stmt -> Either Errors E.Exp
go p =
  case compile' p of
    ([], p') -> Right (E.go p')
    (es, _)  -> Left  es
