module Ceu.Grammar.Full.Compile.Seq where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Full

adjSSeq :: Stmt -> Stmt

adjSSeq (SSeq z (SSeq z' p1 p2) p3) = adjSSeq $ SSeq z p1 (SSeq z' p2 p3)
adjSSeq (SSeq z (SNop _) p)         = adjSSeq p
--adjSSeq (SSeq z p (SNop _))         = adjSSeq p
adjSSeq (SSeq z p1 p2)              = SSeq z (adjSSeq p1) (adjSSeq p2)

adjSSeq p = p
