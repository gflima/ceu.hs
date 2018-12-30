module Ceu.Grammar.Full.Eval where

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (Ann)
import Ceu.Grammar.Type     (Type(..))
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval as E
import Debug.Trace

import Ceu.Grammar.Full.Grammar
import qualified Ceu.Grammar.Full.Compile.Timer    as Timer
import qualified Ceu.Grammar.Full.Compile.Payload  as Payload
import qualified Ceu.Grammar.Full.Compile.Break    as Break
import qualified Ceu.Grammar.Full.Compile.ParAndOr as ParAndOr
import qualified Ceu.Grammar.Full.Compile.Spawn    as Spawn
import qualified Ceu.Grammar.Full.Compile.Pause    as Pause
import qualified Ceu.Grammar.Full.Compile.Async    as Async
import qualified Ceu.Grammar.Full.Compile.Fin      as Fin
import qualified Ceu.Grammar.Full.Compile.Trap     as Trap
import qualified Ceu.Grammar.Full.Compile.Scope    as Scope
import qualified Ceu.Grammar.Full.Compile.Seq      as Seq

import qualified Ceu.Grammar.Check as Check

compile :: Stmt -> (Errors, Stmt)
compile p = --traceShowId $ 
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
    comb Seq.compile      $
      ([], p)
  where
    comb :: (Stmt -> (Errors,Stmt)) -> (Errors,Stmt) -> (Errors,Stmt)
    comb f (es,p) = (es++es',p') where (es',p') = f p

compile' :: Check.Options -> Stmt -> (Errors, G.Stmt)
compile' (o_simp,o_encl,o_prel) p = (es2++es3++es4, p4)
  where
    p0       = if not o_prel then p else
                (Seq z defs p)
    p1       = if not o_encl then p0 else
                (Seq z (Inp z "TIMER" False) (Seq z (Var z "_ret" (Type1 "Int") Nothing) (Seq z (Trap z (Just "_ret") p0) (Halt z))))
    (es2,p2) = compile p1
    (es3,p3) = toGrammar p2
    (es4,p4) = Check.compile (o_simp,False,False) p3
    z        = getAnnS p

    defs = (Seq z (Func  z "(==)" (TypeF (TypeN [(TypeV "a"),  (TypeV "a")])   (Type1 "Bool")))
           (Seq z (Func  z "(+)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
           (Seq z (Func  z "(-)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
           (Seq z (Func  z "(/)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
           (Seq z (Func  z "(*)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
           (Seq z (Func  z "negate" (TypeF (TypeV "a") (TypeV "a")))
           (Seq z (FuncI z "(==)" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Bool")) Nothing)
           (Seq z (FuncI z "(+)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")) Nothing)
           (Seq z (FuncI z "(-)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")) Nothing)
           (Seq z (FuncI z "(/)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")) Nothing)
           (Seq z (FuncI z "(*)"  (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")) Nothing)
                  (FuncI z "negate" (TypeF (Type1 "Int") (Type1 "Int")) Nothing)
           )))))))))))

reaction :: E.Stmt -> In -> (E.Stmt, E.Outs)
reaction p (ext,val) = (p''',outs) where
  (p'',_,_,_,outs) = E.steps (E.bcast ext [] p', 0, [], [], [])
  p' = E.Var ("_INPUT", val) p
  (E.Var _ p''') = p''

evalFullProg :: Stmt -> [In] -> E.Result
evalFullProg prog ins =
  let (es,s) = compile' (True,True,True) prog in
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
