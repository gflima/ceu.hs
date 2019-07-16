module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (Ann, getAnn)
import Ceu.Grammar.Constraints  (cz)
import Ceu.Grammar.Type         (Type(..))
import qualified Ceu.Grammar.Basic    as B
import qualified Ceu.Grammar.TypeSys  as T
import qualified Ceu.Grammar.Simplify as S
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Full.Compile.Data  as Data
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Seq   as Seq
import qualified Ceu.Grammar.Full.Compile.Match as Match
import qualified Ceu.Grammar.Full.Compile.Class as Class
import qualified Ceu.Grammar.Full.Compile.FuncS as FuncS

int   = TData ["Int"]          [] TUnit
bool  = TData ["Bool"]         [] TUnit
boolf = TData ["Bool","False"] [] TUnit
boolt = TData ["Bool","True"]  [] TUnit

prelude :: Ann -> Stmt -> Stmt
prelude z p =
    (Seq z (Data z Nothing (int,  cz) False)  -- TODO: should be abstract
    (Seq z (Data z Nothing (bool, cz) True)
    (Seq z (Data z Nothing (boolf,cz) False)
    (Seq z (Data z Nothing (boolt,cz) False)
    (Seq z (Var  z "_true"  (bool,cz))
    (Seq z (Set  z False (EVar z "_true") (ECons z ["Bool","True"]))
    (Seq z (Var  z "print"  (TFunc (TAny "?")        (TAny "?"), cz))
    (Seq z (Var  z "negate" (TFunc int                int,         cz))
    (Seq z (Var  z "=="     (TFunc (TTuple [int, int]) bool,        cz))
    (Seq z (Var  z "<="     (TFunc (TTuple [int, int]) bool,        cz))
    (Seq z (Var  z "<"      (TFunc (TTuple [int, int]) bool,        cz))
    (Seq z (Var  z "+"      (TFunc (TTuple [int, int]) int,         cz))
    (Seq z (Var  z "-"      (TFunc (TTuple [int, int]) int,         cz))
    (Seq z (Var  z "/"      (TFunc (TTuple [int, int]) int,         cz))
    (Seq z (Var  z "*"      (TFunc (TTuple [int, int]) int,         cz))
    (Seq z (Var  z "rem"    (TFunc (TTuple [int, int]) int,         cz))
           p))))))))))))))))

compile :: Stmt -> Stmt
compile p = Data.compile $ Scope.compile $ Seq.compile $ Match.compile $ Class.compile $ FuncS.compile p

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
