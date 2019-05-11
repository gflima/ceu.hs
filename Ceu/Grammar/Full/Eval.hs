module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann, getAnn)
import Ceu.Grammar.Type     (Type(..))
import qualified Ceu.Grammar.Basic    as B
import qualified Ceu.Grammar.TypeSys  as T
import qualified Ceu.Grammar.Simplify as S
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Seq   as Seq
import qualified Ceu.Grammar.Full.Compile.Match as Match
import qualified Ceu.Grammar.Full.Compile.Class as Class
import qualified Ceu.Grammar.Full.Compile.FuncS as FuncS

prelude :: Ann -> Stmt -> Stmt
prelude z p =
    (Seq z (Data z ["Int"]        [] Type0 True)
    (Seq z (Data z ["Bool"]       [] Type0 True)
    (Seq z (Data z ["Bool.True"]  [] Type0 False)
    (Seq z (Data z ["Bool.False"] [] Type0 False)
    (Seq z (Var  z "_true"  (TypeD ["Bool"]))
    (Seq z (Set  z False (LVar "_true") (Cons z ["Bool","True"] (Unit z)))
    (Seq z (Var  z "print"  (TypeF (TypeV "?" [])                         (TypeV "?" [])))
    (Seq z (Var  z "negate" (TypeF (TypeD ["Int"])                        (TypeD ["Int"])))
    (Seq z (Var  z "=="     (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Bool"])))
    (Seq z (Var  z "<="     (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Bool"])))
    (Seq z (Var  z "<"      (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Bool"])))
    (Seq z (Var  z "+"      (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Int"])))
    (Seq z (Var  z "-"      (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Int"])))
    (Seq z (Var  z "/"      (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Int"])))
    (Seq z (Var  z "*"      (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Int"])))
    (Seq z (Var  z "rem"    (TypeF (TypeN [TypeD ["Int"], TypeD ["Int"]]) (TypeD ["Int"])))
           p))))))))))))))))

compile :: Stmt -> Stmt
compile p = Scope.compile $ Seq.compile $ Match.compile $ Class.compile $ FuncS.compile p

compile' :: Stmt -> (Errors, B.Stmt)
compile' p = (es4, p4)
  where
    p1       = compile p
    p2       = toBasicStmt p1
    p3       = S.go p2
    (es4,p4) = T.go p3

go :: Stmt -> Either Errors E.Exp
go p =
  case compile' p of
    ([], p') -> Right (E.go' p')
    (es, _)  -> Left  es
