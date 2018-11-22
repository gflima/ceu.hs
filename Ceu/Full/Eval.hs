module Ceu.Full.Eval where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Ceu.Grammar.Check (Options)
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
import qualified Ceu.Full.Trap    as Trap

import qualified Ceu.Grammar.Check as Check

compile :: Stmt -> (Errors, Stmt)
compile p =
    comb Forever.compile $
    comb Timer.compile   $
    comb Payload.compile $
    comb Break.compile   $
    comb AndOr.compile   $
    comb Spawn.compile   $
    comb Pause.compile   $
    comb Async.compile   $
    comb Fin.compile     $
    comb Trap.compile    $
      ([], p)
  where
    comb :: (Stmt -> (Errors,Stmt)) -> (Errors,Stmt) -> (Errors,Stmt)
    comb f (es,p) = (es++es',p') where (es',p') = f p

compile' :: Options -> Stmt -> (Errors, G.Stmt)
compile' opts p = (es'++es''++es''', p''')
  where
    (es',  p')   = compile p
    (es'', p'')  = toGrammar p'
    (es''',p''') = Check.compile opts p''

reaction :: E.Stmt -> In -> (E.Stmt,E.Outs)
reaction p (ext,val) = (p''',outs) where
  (p'',_,_,_,outs) = E.steps (E.bcast ext [] p', 0, [], [], [])
  p' = E.Var (("_"++ext), val) p
  (E.Var _ p''') = p''

evalFullProg :: Stmt -> [In] -> E.Result
evalFullProg prog ins =
  let (es,s) = compile' (True,True) prog in
    if es == [] then
      let res = E.run s ins'' reaction in
        case res of
          E.Success (val,outss) -> E.Success (val, Timer.join ins' outss)
          otherwise             -> res
    else
      E.Fail es
    where
      ins'  = ("BOOT",Nothing):ins
      ins'' = Timer.expand ins'
