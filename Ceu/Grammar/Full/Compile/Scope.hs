module Ceu.Grammar.Full.Compile.Scope where

import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type             (Type(..))
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

remSScope :: Stmt -> Stmt
remSScope (SScope _ p) = p
remSScope p = p

-------------------------------------------------------------------------------

setScope :: Stmt -> Stmt

setScope (SClass'' z id  cs ifc)       = SClassS z id  cs  ifc       (SNop z)
setScope (SInst''  z cls tp imp)       = SInstS  z cls tp  imp       (SNop z)
setScope (SData    z tp nms st cs abs) = SDataS  z tp  nms st cs abs (SNop z)
setScope (SVar'    z var _ tp ini)     = SVarS   z var tp  ini       (SNop z)
setScope (STodo    z str)              = STodoS  z str               (SNop z)

setScope (SSeq _ (SClassS z id  cs ifc       (SNop _)) p2) = SClassS z id  cs  ifc       p2
setScope (SSeq _ (SInstS  z cls tp imp       (SNop _)) p2) = SInstS  z cls tp  imp       p2
setScope (SSeq _ (SDataS  z tp nms st cs abs (SNop _)) p2) = SDataS  z tp  nms st cs abs p2
setScope (SSeq _ (SVarS   z var tp ini       (SNop _)) p2) = SVarS   z var tp  ini       p2
setScope (SSeq _ (STodoS  z str              (SNop _)) p2) = STodoS  z str               p2

setScope p = p
