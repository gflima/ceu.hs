module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import qualified Ceu.Grammar.Grammar as G
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Timer    as Timer
import qualified Ceu.Grammar.Full.Compile.Forever  as Forever
import qualified Ceu.Grammar.Full.Compile.Payload  as Payload
import qualified Ceu.Grammar.Full.Compile.Break    as Break
import qualified Ceu.Grammar.Full.Compile.ParAndOr as ParAndOr
import qualified Ceu.Grammar.Full.Compile.Spawn    as Spawn
import qualified Ceu.Grammar.Full.Compile.Pause    as Pause
import qualified Ceu.Grammar.Full.Compile.Async    as Async
import qualified Ceu.Grammar.Full.Compile.Fin      as Fin
import qualified Ceu.Grammar.Full.Compile.Trap     as Trap
import qualified Ceu.Grammar.Full.Compile.Scope    as Scope

import qualified Ceu.Grammar.Check.Check as Check

compile :: Stmt -> (Errors, Stmt)
compile p =
    comb Forever.compile  $
    comb Timer.compile    $
    comb Payload.compile  $
    comb Break.compile    $
    comb ParAndOr.compile $
    comb Spawn.compile    $
    comb Pause.compile    $
    comb Async.compile    $
    comb Fin.compile      $
    comb Trap.compile     $
    comb Scope.compile    $
      ([], p)
  where
    comb :: (Stmt -> (Errors,Stmt)) -> (Errors,Stmt) -> (Errors,Stmt)
    comb f (es,p) = (es++es',p') where (es',p') = f p

compile' :: Check.Options -> Stmt -> (Errors, G.Stmt)
compile' (o_simp,o_encl) p = (es2++es3++es4, p4)
  where
    p1       = if not o_encl then p else
                (Seq (Var "_ret" Nothing) (Seq (Trap (Just "_ret") p) (AwaitFor)))
    (es2,p2) = compile p1
    (es3,p3) = toGrammar p2
    (es4,p4) = Check.compile (o_simp,False) p3

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
          Right (val,outss) -> Right (val, Timer.join ins' outss)
          otherwise         -> res
    else
      Left es
    where
      ins'  = ("BOOT",Nothing):ins
      ins'' = Timer.expand ins'
