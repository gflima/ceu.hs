module Ceu.Full.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Full.Grammar
import qualified Ceu.Full.Timer   as Timer
import qualified Ceu.Full.Forever as Forever
import qualified Ceu.Full.Payload as Payload
import qualified Ceu.Full.Break   as Break
import qualified Ceu.Full.AndOr   as AndOr
import qualified Ceu.Full.Spawn   as Spawn
import qualified Ceu.Full.Pause   as Pause
import qualified Ceu.Full.Async   as Async
import qualified Ceu.Full.Fin     as Fin

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG $ Forever.remove $ Timer.remove $ Payload.remove
                  $ Break.remove $ AndOr.remove $ Spawn.remove $ Spawn.check
                  $ Pause.remove $ Async.remove $ Fin.remove
                  $ p where
  toG :: Stmt -> G.Stmt
  toG (Var id Nothing p) = G.Var id (toG p)
  toG (Int id b p)       = G.Int id (toG p)
  toG (Write id exp)     = G.Write id exp
  toG (AwaitExt ext var) = G.AwaitExt ext
  toG (EmitExt ext exp)  = G.EmitExt ext exp
  toG (AwaitInt int var) = G.AwaitInt int
  toG (EmitInt int val)  = G.EmitInt int
  toG (If exp p1 p2)     = G.If exp (toG p1) (toG p2)
  toG (Seq p1 p2)        = G.Seq (toG p1) (toG p2)
  toG (Loop p)           = G.Loop (toG p)
  toG (Every evt var p)  = G.Every evt (toG p)
  toG (Error msg)        = G.Error msg
  toG (Par' p1 p2)       = G.Par (toG p1) (toG p2)
  toG (Pause' var p)     = G.Pause var (toG p)
  toG (Fin' p)           = G.Fin (toG p)
  toG (Trap' p)          = G.Trap (toG p)
  toG (Escape' n)        = G.Escape n
  toG Nop                = G.Nop
  toG p                  = error $ "toG: unexpected statement: "++(show p)

reaction :: E.Stmt -> In -> (E.Stmt,E.Outs)
reaction p (ext,val) = (p''',outs) where
  (p'',_,_,_,outs) = E.steps (E.bcast ext [] p', 0, [], [], [])
  p' = E.Var (("_"++ext), val) p
  (E.Var _ p''') = p''

evalFullProg :: Stmt -> [In] -> (Val,[E.Outs])
evalFullProg prog ins = (val,outss')
  where
    (val,outss) = E.evalProg_Reaction (toGrammar prog) ins'' reaction
    ins'   = ("BOOT",Nothing):ins
    ins''  = Timer.expand ins'
    outss' = Timer.join ins' outss
