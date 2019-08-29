module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Full

compile :: Stmt -> Stmt
compile p = map_stmt (remScope,id,id) $ map_stmt (stmt,id,id) p
              where
                remScope (SScope _ p) = p
                remScope p = p

stmt :: Stmt -> Stmt

stmt (SClass' z id  cs ifc)       = SClass'' z id  cs ifc       (SNop z)
stmt (SInst'  z cls tp imp)       = SInst''  z cls tp imp       (SNop z)
stmt (SData   z tp nms st cs abs) = SData''  z tp nms st cs abs (SNop z)
stmt (SVar    z var tp)           = SVar''   z var tp           (SNop z)

stmt (SSeq _ (SClass'' z id  cs ifc       (SNop _)) p2) = SClass'' z id  cs ifc       p2
stmt (SSeq _ (SInst''  z cls tp imp       (SNop _)) p2) = SInst''  z cls tp imp       p2
stmt (SSeq _ (SData''  z tp nms st cs abs (SNop _)) p2) = SData''  z tp nms st cs abs p2
stmt (SSeq _ (SVar''   z var tp           (SNop _)) p2) = SVar''   z var tp           p2

stmt p = p
