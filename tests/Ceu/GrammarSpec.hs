module Ceu.GrammarSpec (main, spec) where

import Ceu.Grammar.Globals (Errors)
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import qualified Ceu.Grammar.Check  as Check
import qualified Ceu.Grammar.VarEvt as VarEvt
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "checkLoop () -- matching-Break/AwaitExt/Every () in all paths" $ do

    -- atomic statements --
    checkLoopIt (Loop () (Write () "x" (Umn () (Const () 1)))) False
    checkLoopIt (Loop () (AwaitExt () "A"))              True
    checkLoopIt (Loop () (AwaitInt () "a"))              False
    checkLoopIt (Loop () (EmitInt () "a"))               False
    checkLoopIt (Loop () (Escape () 0))                  True
    checkLoopIt (Loop () (Loop () (Escape () 0)))        True
    checkLoopIt (Loop () ((Nop ())))                     False
    checkLoopIt (Loop () (Error () ""))                  False

    -- compound statements --
    checkLoopIt (Loop () (Var () "x" (Var () "y" (Escape () 0))))         True
    checkLoopIt (Loop () (Var () "x" (Var () "y" (Nop ()))))              False

    checkLoopIt (Loop () (If () (Const () 0) (Escape () 0) (Nop ())))     False
    checkLoopIt (Loop () (If () (Const () 0) (Fin () (Nop ())) (Nop ()))) False
    checkLoopIt (Loop () (If () (Const () 0) (Every () "A" (Nop ())) (AwaitExt () "A"))) True

    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Escape () 0) `sSeq` (Nop ()))) True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0))))               False
    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Loop () (Escape () 0))))   True
    checkLoopIt (Loop () ((Escape () 0) `sSeq` Loop () (Nop ())))         True
    checkLoopIt (Loop () ((Nop ()) `sSeq` Loop () (Nop ())))              False

    checkLoopIt (Loop () (Loop () (Loop () (AwaitExt () "A"))))           True
    checkLoopIt (Loop () (Loop () (Escape () 0)))                         True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0))))               False
    checkLoopIt (Loop () (Loop () (Trap () (Loop () (Escape () 0)))))     False
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0)) `sSeq` (Trap () (Loop () (Escape () 0))))) False
    checkLoopIt (Loop () (Loop () (AwaitExt () "A") `sSeq` Loop () (Nop ()))) True
    checkLoopIt (Loop () (Loop () (Seq () (Escape () 0) (Escape () 0))))  True
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) False
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 1))))) False

    checkLoopIt (Loop () ((Nop ()) `sPar` (Nop ()) `sPar` (Nop ())))      False
    checkLoopIt (Loop () (Pause () "a" (Nop ())))                         False
    checkLoopIt (Loop () (Every () "A" (Nop ()) `sPar` AwaitExt () "A" `sPar` (Escape () 0))) True
    checkLoopIt (Loop () (Pause () "a" (AwaitExt () "A")))                True

    -- Fin () always run in zero time.
    checkLoopIt (Loop () (Fin () (Nop ())))                               False
    checkLoopIt (Loop () (Fin () (Escape () 0)))                          False
    checkLoopIt (Loop () (Fin () (AwaitExt () "A")))                      False
    checkLoopIt (Loop () (Fin () (Every () "A" (Nop ()))))                False

  --------------------------------------------------------------------------
  describe "checkFin/Every () -- no Loop/Escape/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin () (Write () "x" (Const () 0))) []
    checkFinIt (Fin () (AwaitExt () "A"))        ["await: invalid statement"]
    checkFinIt (Fin () (AwaitInt () "a"))        ["await: invalid statement"]
    checkFinIt (Fin () (EmitInt () "a"))         []
    checkFinIt (Fin () (Escape () 0))            ["escape: invalid statement"]
    checkFinIt (Fin () ((Nop ())))               []
    checkFinIt (Fin () (Error () ""))            []

    -- compound statements --
    checkFinIt (Fin () (Var () "x" (Nop ())))                []
    checkFinIt (Fin () (Var () "x" (Every () "A" (Nop ())))) ["every: invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Loop () (Escape () 0)) ((Nop ())))) ["escape: invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Write () "x" (Const () 0)) ((Nop ())))) []
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (AwaitExt () "A") `sSeq` (Nop ()))) ["await: invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (EmitInt () "a") `sSeq` (Nop ())))  []
    checkFinIt (Fin () (Loop () (AwaitInt () "a")))          ["await: invalid statement"]
    checkFinIt (Fin () (Loop () (AwaitExt () "A")))          ["await: invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sPar` (Nop ()) `sPar` (EmitInt () "a"))) ["parallel: invalid statement","parallel: invalid statement"]

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkCheckIt (Error () "")               []
    checkCheckIt (Escape () 0)               ["escape: orphan `escape` statement"]
    checkCheckIt (Write () "x" (Const () 0)) ["assignment: variable 'x' is not declared"]

    -- compound statements --
    checkCheckIt (Trap () (Escape () 0))     []
    checkCheckIt (Trap () (Escape () 1))     ["escape: orphan `escape` statement", "trap: missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 0))) ["trap: terminating `trap` body","trap: missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 1))) ["trap: missing `escape` statement"]
    checkCheckIt (Trap () (Seq () (Escape () 0) (Escape () 1))) ["escape: orphan `escape` statement","escape: unreachable statement"]
    checkCheckIt (Trap () (Seq () (Escape () 1) (Escape () 1))) ["escape: orphan `escape` statement","escape: orphan `escape` statement","escape: unreachable statement", "trap: missing `escape` statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkStmtsIt (Error () "")               []
    checkStmtsIt (Write () "x" (Const () 0)) []

    -- compound statements --
    checkStmtsIt (Seq () (Escape () 1) (Escape () 0)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Trap () (Escape () 1))) (Escape () 0)) ["trap: missing `escape` statement"]
    checkStmtsIt (Seq () (Escape () 0) (Escape () 1)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (AwaitExt () "FOREVER") (Escape () 1)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (Seq () (AwaitExt () "FOREVER") (Nop ())) (Escape () 1)) ["nop: unreachable statement",("escape: unreachable statement")]
    checkStmtsIt (Seq () (Loop () (Nop ())) (Nop ())) ["loop: unbounded `loop` execution","nop: unreachable statement"]
    checkStmtsIt (Seq () (Every () "" (Nop ())) (Nop ())) ["nop: unreachable statement"]
    checkStmtsIt (Seq () (Par () (Nop ()) (Every () "" (Nop ()))) (Nop ())) ["parallel: terminating trail","nop: unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Escape () 1))))) (Nop ())) ["escape: unreachable statement","loop: unbounded `loop` execution"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["nop: unreachable statement", "loop: unbounded `loop` execution","trap: missing `escape` statement","nop: unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkVarEvt -- declarations" $ do

    checkVarEvtIt (Nop ())                                 []
    checkVarEvtIt (Var () "a" (Nop ()))                    []
    checkVarEvtIt (Var () "a" (Write () "a" (Const () 1))) []
    checkVarEvtIt (Var () "a" (Var () "a" (Nop ())))       ["declaration: variable 'a' is already declared"]
    checkVarEvtIt (Int () "e" (Int () "e" (Nop ())))       ["declaration: event 'e' is already declared"]
    checkVarEvtIt (Write () "a" (Const () 1))              ["assignment: variable 'a' is not declared"]
    checkVarEvtIt (AwaitInt () "e")                        ["await: event 'e' is not declared"]
    checkVarEvtIt (Every () "e" (Nop ()))                  ["every: event 'e' is not declared"]
    checkVarEvtIt (Pause () "a" (Nop ()))                  ["pause/if: variable 'a' is not declared"]
    checkVarEvtIt (Var () "a" (Write () "a" (Umn () (Read () "b")))) ["read access to 'b': variable 'b' is not declared"]

  --------------------------------------------------------------------------
  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Write () "c" (Const () 0)) []
    checkStmtsIt (AwaitExt () "A")        []
    checkStmtsIt (AwaitInt () "a")        []
    checkStmtsIt (EmitInt () "a")         []
    checkStmtsIt (Escape () 0)            []
    checkStmtsIt ((Nop ()))               []
    checkStmtsIt (Error () "")            []

    -- compound statements --
    checkStmtsIt (Var () "x" (Nop ()))                 []
    checkStmtsIt (If () (Const () 0) (Nop ()) (Escape () 0)) []
    checkStmtsIt (Seq () (Escape () 0) (Nop ()))       ["nop: unreachable statement"]
    checkStmtsIt (Loop () (Escape () 0))               ["loop: `loop` never iterates"]
    checkStmtsIt (Loop () (Nop ()))                    ["loop: unbounded `loop` execution"]
    checkStmtsIt (Every () "A" (Nop ()))               []
    checkStmtsIt (Every () "A" (Fin () (Nop ())))      ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Par () (Escape () 0) (Nop ()))       ["parallel: terminating trail"]
    checkStmtsIt (Par () (Escape () 0) (AwaitExt () "FOREVER")) []
    checkStmtsIt (Par () (AwaitExt () "FOREVER") (Seq () (EmitInt () "a") (AwaitExt () "FOREVER"))) []
    checkStmtsIt (Par () (Nop ()) (EmitInt () "a"))    ["parallel: terminating trail"]
    checkStmtsIt (Pause () "a" (Nop ()))               []
    checkStmtsIt (Fin () (Nop ()))                     []
    checkStmtsIt (Fin () (Fin () (Nop ())))            ["finalize: invalid statement in `finalize`", "finalize: invalid statement"]

    -- misc --
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Escape () 0)))) ["loop: `loop` never iterates","finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Nop ())))) ["loop: unbounded `loop` execution"]
    checkStmtsIt (Var () "x" (Fin () (Every () "A" (Nop ())))) ["finalize: invalid statement in `finalize`", "every: invalid statement"]
    checkStmtsIt (Loop () (Trap () (Loop () (Escape () 0))))   ["loop: `loop` never iterates","loop: unbounded `loop` execution"]
    checkStmtsIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) ["escape: unreachable statement","loop: `loop` never iterates","loop: unbounded `loop` execution"]
    checkStmtsIt (AwaitInt () "a" `sSeq` (Fin () (Escape () 0)) `sPar` (AwaitExt () "FOREVER")) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (AwaitInt () "a" `sSeq` (Every () "A" (Fin () (Nop ()))) `sPar` (AwaitExt () "FOREVER")) ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Loop () ((AwaitExt () "FOREVER") `sPar` Loop () (Loop () (Loop () (AwaitExt () "A")))))  ["loop: `loop` never iterates","loop: `loop` never iterates","loop: `loop` never iterates"]
    checkStmtsIt (Loop () ((Escape () 0) `sPar` Loop () (Loop () (Loop () (AwaitExt () "A"))))) ["loop: `loop` never iterates","loop: `loop` never iterates","loop: `loop` never iterates"]
    checkStmtsIt (Fin () (Escape () 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Loop () (AwaitExt () "FOREVER")) ["loop: `loop` never iterates"]

    -- all
    checkCheckIt (Fin () (Escape () 0)) ["escape: orphan `escape` statement", "finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Trap () (Fin () (Escape () 0))) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["nop: unreachable statement", "loop: unbounded `loop` execution", "trap: missing `escape` statement", "nop: unreachable statement"]
    checkCheckIt (Trap () (Seq () (Trap () (Par () (AwaitExt () "FOREVER") (Escape () 0))) (Escape () 0)))
      []
    checkCheckIt (Trap () (Par () (Escape () 0) (Seq () (Par () (AwaitExt () "FOREVER") (Fin () (Nop ()))) (Escape () 0))))
      ["escape: unreachable statement"]

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt  Check.boundedLoop p b
        checkFinIt (Fin () p) b = checkIt' Check.getComplexs p b
        checkEveryIt p b     = checkIt' Check.getComplexs p b
        checkVarEvtIt p b    = checkIt' VarEvt.check p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt :: Stmt () -> Errors -> Spec
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False))) p b
