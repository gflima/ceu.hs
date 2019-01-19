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
import qualified Ceu.Grammar.Full.Compile.FuncS as FuncS

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

compile :: Stmt -> Stmt
compile p = Scope.compile $ Seq.compile $ FuncS.compile p

compile' :: Stmt -> (Errors, B.Stmt)
compile' p = (es3, p3)
  where
    p1       = compile p
    p2       = toBasicStmt p1
    (es3,p3) = T.go p2

go :: Stmt -> Either Errors E.Exp
go p =
  case compile' p of
    ([], p') -> Right (E.go p')
    (es, _)  -> Left  es
