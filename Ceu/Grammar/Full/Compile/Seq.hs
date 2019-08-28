module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = map_stmt (stmt,id,id) p

stmt :: Stmt -> Stmt

stmt (SSeq z (SSeq z' p1 p2) p3) = stmt $ SSeq z p1 (SSeq z' p2 p3)
stmt (SSeq z p1 p2)              = SSeq z (stmt p1) (stmt p2)

stmt p = p
