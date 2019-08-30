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

setScope (SClass' z id  cs ifc)       = SClass'' z id  cs ifc       (SNop z)
setScope (SInst'  z cls tp imp)       = SInst''  z cls tp imp       (SNop z)
setScope (SData   z tp nms st cs abs) = SData''  z tp nms st cs abs (SNop z)
setScope (SVar    z var tp)           = SVar''   z var tp           (SNop z)

setScope (SSeq _ (SClass'' z id  cs ifc       (SNop _)) p2) = SClass'' z id  cs ifc       p2
setScope (SSeq _ (SInst''  z cls tp imp       (SNop _)) p2) = SInst''  z cls tp imp       p2
setScope (SSeq _ (SData''  z tp nms st cs abs (SNop _)) p2) = SData''  z tp nms st cs abs p2
setScope (SSeq _ (SVar''   z var tp           (SNop _)) p2) = SVar''   z var tp           p2

setScope p = p
