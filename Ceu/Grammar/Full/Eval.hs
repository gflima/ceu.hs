module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (Ann, getAnn)
import Ceu.Grammar.Constraints  (cz)
import Ceu.Grammar.Type         (Type(..), FuncType(..))
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
import qualified Ceu.Grammar.Full.Compile.Func  as Func

int   = TData False ["Int"]          []
bool  = TData False ["Bool"]         []
boolf = TData False ["Bool","False"] []
boolt = TData False ["Bool","True"]  []

prelude :: Ann -> Stmt -> Stmt
prelude z p =
    (SSeq z (SData z int   Nothing TUnit cz False)  -- TODO: should be abstract
    (SSeq z (SData z bool  Nothing TUnit cz True)
    (SSeq z (SData z boolf Nothing TUnit cz False)
    (SSeq z (SData z boolt Nothing TUnit cz False)
    (SSeq z (SVar  z "_true"  (bool,cz)                          (Just $ ECons z ["Bool","True"]))
    (SSeq z (SVar  z "print"  (TFunc FuncGlobal (TVar False "?")    (TVar False "?"), cz) Nothing)
    (SSeq z (SVar  z "negate" (TFunc FuncGlobal int                 int,              cz) Nothing)
    (SSeq z (SVar  z "=="     (TFunc FuncGlobal (TTuple [int, int]) bool,             cz) Nothing)
    (SSeq z (SVar  z "<="     (TFunc FuncGlobal (TTuple [int, int]) bool,             cz) Nothing)
    (SSeq z (SVar  z "<"      (TFunc FuncGlobal (TTuple [int, int]) bool,             cz) Nothing)
    (SSeq z (SVar  z "+"      (TFunc FuncGlobal (TTuple [int, int]) int,              cz) Nothing)
    (SSeq z (SVar  z "-"      (TFunc FuncGlobal (TTuple [int, int]) int,              cz) Nothing)
    (SSeq z (SVar  z "/"      (TFunc FuncGlobal (TTuple [int, int]) int,              cz) Nothing)
    (SSeq z (SVar  z "*"      (TFunc FuncGlobal (TTuple [int, int]) int,              cz) Nothing)
    (SSeq z (SVar  z "rem"    (TFunc FuncGlobal (TTuple [int, int]) int,              cz) Nothing)
           p)))))))))))))))

compile :: Stmt -> Stmt
compile p =
  map_stmt (Scope.remSScope,id,id)      $
  map_stmt (Match.remSSetSIf,id,id)     $
  map_stmt (Match.remIni,id,id)         $
  map_stmt (id,Func.remEFuncPar,id)     $
  map_stmt (Data.addAccs,id,id)         $
  Data.expHier []                       $
  map_stmt (Scope.setScope,id,id)       $
  map_stmt (Seq.adjSSeq,id,id)          $
  map_stmt (Class.remClassInst,id,id)   $
  map_stmt (Class.addInstCall,id,id)    $
  map_stmt (Class.insDict,id,id)        $
  map_stmt (Class.insWrappers,id,id)    $
  map_stmt (Class.dupRenImpls,id,id)    $
  map_stmt (Class.dclClassDicts,id,id)       $
  map_stmt (Class.insConstraint,id,id)  $
  map_stmt (Func.remSFunc,id,id)        $
  p where

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
