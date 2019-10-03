module Ceu.Grammar.Full.Eval where

import qualified Data.Map as Map

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

cat0 :: (Stmt -> Stmt) -> (Errors,Stmt) -> (Errors,Stmt)
cat0 f (es1,p1) = (es1,p2) where
                    p2 = f p1

catE :: (Stmt -> (Errors,Stmt)) -> (Errors,Stmt) -> (Errors,Stmt)
catE f (es1,p1) = (es1++es2,p2) where
                    (es2,p2) = f p1

compile :: Stmt -> (Errors,Stmt)
compile p = --cat0 traceStmt $
  cat0 (map_stmt' (f2 Match.remSSetSIf,id,id))      $
  cat0 (map_stmt' (f2 Match.remIni,id,id))          $
  cat0 (map_stmt' (id2,Func.remEFuncPar,id))        $
  --traceShowId $
  cat0 (map_stmt' (f2 Data.addAccs,id,id))          $
  cat0 (Data.expHier [])                            $ --traceShowId $
--
{-
  map_stmt' (Class.uniInstProtos,id,id)       $   -- uses scope (clss)
--
  map_stmt' (f2 Class.addInstCall,id,id)      $
  map_stmt' (f2 Class.addGenWrappers,id,id)   $
  map_stmt' (Class.dupRenImpls,id,id)         $
--
  map_stmt' (f2 Class.addProtosGen,id,id)     $
-}
  cat0 (map_stmt' (f2 Class.dclClassDicts,id,id))   $
  cat0 (map_stmt' (f2 Class.inlClassInst,id,id))    $
    -- addInstDicts
  cat0 (map_stmt' (f2 Class.addGenDict,id,id))      $
  cat0 (map_stmt' (f2 Class.addGCallBody,id,id))    $
  cat0 (map_stmt' (f2 Class.addInstGCalls,id,id))   $
  catE (Class.withEnvS [])                          $
    -- addClassToInst
    -- addGGenWrappers
    -- repGGenInsts
  cat0 (map_stmt' (f2 Class.setGen',id,id))         $
  cat0 (map_stmt' (f2 Class.setGen,id,id))          $
  cat0 (map_stmt' (f2 Class.addClassCs,id,id))      $
--
  cat0 (map_stmt' (f2 Scope.remSScope,id,id))       $
  cat0 (map_stmt' (f2 Scope.setScope,id,id))        $
  cat0 (map_stmt' (f2 Seq.adjSSeq,id,id))           $   -- no more SSeq
  cat0 (map_stmt' (f2 Func.remSFunc,id,id))         $
    ([],p)

rmdups :: (Eq a) => [a] -> [a]
rmdups [] = []
rmdups [x] = [x]
rmdups (x:xs) = x : [ k  | k <- rmdups(xs), k /= x ]

compile' :: Stmt -> (Errors, B.Stmt)
compile' p = (rmdups (es1++es4), p4)
  where
    (es1,p1) = compile p
    p2       = toBasicStmt p1
    p3       = S.go p2
    (es4,p4) = T.go p3

go :: Stmt -> Either Errors E.Exp
go p =
  case compile' p of
    ([], p') -> Right (E.go' p')
    (es, _)  -> Left  es
