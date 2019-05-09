module Ceu.Grammar.Full.Compile.FuncS where

import Debug.Trace
import qualified Data.Set as S

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full
import qualified Ceu.Grammar.Type as T

compile :: Stmt -> Stmt
compile p = stmt p

stmt :: Stmt -> Stmt
stmt (Class z (cls,[var]) exts ifc) = Class z (cls,[var]) exts (stmt $ aux ifc)
  where
    aux (Seq   z p1 p2)     = Seq   z (aux p1) (aux p2)
    aux (Var   z id _ tp)   = Var   z id True (T.addConstraint (var,cls) tp)
    aux (FuncS z id tp imp) = FuncS z id (T.addConstraint (var,cls) tp) imp
    aux p                   = p

stmt (Inst  z me imp)        = Inst  z me     (stmt imp)
--stmt (FuncS z id gen tp imp) = Seq z (Var z id gen tp) (Set z False (LVar id) (Func z tp imp))

stmt (FuncS z k tp imp)      = Seq z (Var z k gen tp) (Set z False (LVar k) (Func z tp imp'))
 where
  (gen,imp') = case S.toList $ T.getConstraints tp of
    []            -> (False, imp)
    --[(var,[cls])] -> (True,  imp)
    [(var,[cls])] -> (True,  (map_stmt (id,id,T.addConstraint(var,cls)) imp))

{-
              return $  -- TODO: remover tudo e fazer em Full.FuncS
                case Set.toList $ getConstraints tp of
                  []            -> FuncS ann f tp imp
                  [(var,[cls])] -> FuncS ann f tp (map_stmt (id,id,addConstraint(var,cls)) imp)
-}

stmt (Set   z chk loc exp)   = Set z chk loc (expr exp)
stmt (Match z loc exp p1 p2) = Match z loc (expr exp) (stmt p1) (stmt p2)
stmt (CallS z exp)           = CallS z (expr exp)
stmt (If    z exp p1 p2)     = If z (expr exp) (stmt p1) (stmt p2)
stmt (Seq   z p1 p2)         = Seq z (stmt p1) (stmt p2)
stmt (Loop  z p)             = Loop z (stmt p)
stmt (Scope z p)             = Scope z (stmt p)
stmt (Ret   z exp)           = Ret z (expr exp)
stmt p                       = p

expr :: Exp -> Exp
expr (Call z e1 e2)          = Call z (expr e1) (expr e2)
expr (Func z tp p)           = Func z tp (stmt p)
expr e                       = e
