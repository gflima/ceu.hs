module Ceu.GrammarSpec (main, spec) where

import Ceu.Grammar.Globals (Errors, Ann(..))
import Ceu.Grammar.Ann.Unit
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import qualified Ceu.Grammar.Check  as Check
import qualified Ceu.Grammar.Id as Id
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "checkLoop () -- matching-Break/AwaitInp/Every () in all paths" $ do

    -- atomic statements --
    checkLoopIt (Loop () (Write () "x" (Umn () (Const () 1)))) False
    checkLoopIt (Loop () (AwaitInp () "A"))              True
    checkLoopIt (Loop () (AwaitEvt () "a"))              False
    checkLoopIt (Loop () (EmitEvt () "a"))               False
    checkLoopIt (Loop () (Escape () 0))                  True
    checkLoopIt (Loop () (Loop () (Escape () 0)))        True
    checkLoopIt (Loop () ((Nop ())))                     False
    checkLoopIt (Loop () (Error () ""))                  False

    -- compound statements --
    checkLoopIt (Loop () (Var () "x" (Var () "y" (Escape () 0))))         True
    checkLoopIt (Loop () (Var () "x" (Var () "y" (Nop ()))))              False

    checkLoopIt (Loop () (If () (Const () 0) (Escape () 0) (Nop ())))     False
    checkLoopIt (Loop () (If () (Const () 0) (Fin () (Nop ())) (Nop ()))) False
    checkLoopIt (Loop () (If () (Const () 0) (Every () "A" (Nop ())) (AwaitInp () "A"))) True

    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Escape () 0) `sSeq` (Nop ()))) True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0))))               False
    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Loop () (Escape () 0))))   True
    checkLoopIt (Loop () ((Escape () 0) `sSeq` Loop () (Nop ())))         True
    checkLoopIt (Loop () ((Nop ()) `sSeq` Loop () (Nop ())))              False

    checkLoopIt (Loop () (Loop () (Loop () (AwaitInp () "A"))))           True
    checkLoopIt (Loop () (Loop () (Escape () 0)))                         True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0))))               False
    checkLoopIt (Loop () (Loop () (Trap () (Loop () (Escape () 0)))))     False
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0)) `sSeq` (Trap () (Loop () (Escape () 0))))) False
    checkLoopIt (Loop () (Loop () (AwaitInp () "A") `sSeq` Loop () (Nop ()))) True
    checkLoopIt (Loop () (Loop () (Seq () (Escape () 0) (Escape () 0))))  True
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) False
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 1))))) False

    checkLoopIt (Loop () ((Nop ()) `sPar` (Nop ()) `sPar` (Nop ())))      False
    checkLoopIt (Loop () (Pause () "a" (Nop ())))                         False
    checkLoopIt (Loop () (Every () "A" (Nop ()) `sPar` AwaitInp () "A" `sPar` (Escape () 0))) True
    checkLoopIt (Loop () (Pause () "a" (AwaitInp () "A")))                True

    -- Fin () always run in zero time.
    checkLoopIt (Loop () (Fin () (Nop ())))                               False
    checkLoopIt (Loop () (Fin () (Escape () 0)))                          False
    checkLoopIt (Loop () (Fin () (AwaitInp () "A")))                      False
    checkLoopIt (Loop () (Fin () (Every () "A" (Nop ()))))                False

  --------------------------------------------------------------------------
  describe "checkFin/Every () -- no Loop/Escape/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin () (Write () "x" (Const () 0))) []
    checkFinIt (Fin () (AwaitInp () "A"))        ["await: invalid statement"]
    checkFinIt (Fin () (AwaitEvt () "a"))        ["await: invalid statement"]
    checkFinIt (Fin () (EmitEvt () "a"))         []
    checkFinIt (Fin () (Escape () 0))            ["escape: invalid statement"]
    checkFinIt (Fin () ((Nop ())))               []
    checkFinIt (Fin () (Error () ""))            []

    -- compound statements --
    checkFinIt (Fin () (Var () "x" (Nop ())))                []
    checkFinIt (Fin () (Var () "x" (Every () "A" (Nop ())))) ["every: invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Loop () (Escape () 0)) ((Nop ())))) ["escape: invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Write () "x" (Const () 0)) ((Nop ())))) []
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (AwaitInp () "A") `sSeq` (Nop ()))) ["await: invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (EmitEvt () "a") `sSeq` (Nop ())))  []
    checkFinIt (Fin () (Loop () (AwaitEvt () "a")))          ["await: invalid statement"]
    checkFinIt (Fin () (Loop () (AwaitInp () "A")))          ["await: invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sPar` (Nop ()) `sPar` (EmitEvt () "a"))) ["parallel: invalid statement","parallel: invalid statement"]

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkCheckIt (Error () "")               []
    checkCheckIt (Escape () 0)               ["escape: orphan `escape` statement"]
    checkCheckIt (Write () "x" (Const () 0)) ["assignment: identifier 'x' is not declared"]

    -- compound statements --
    checkCheckIt (Trap () (Escape () 0))     []
    checkCheckIt (Trap () (Escape () 1))     ["escape: orphan `escape` statement", "trap: missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 0))) ["trap: terminating `trap` body","trap: missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 1))) ["trap: missing `escape` statement"]
    checkCheckIt (Trap () (Seq () (Escape () 0) (Escape () 1))) ["escape: orphan `escape` statement","escape: unreachable statement"]
    checkCheckIt (Trap () (Seq () (Escape () 1) (Escape () 1))) ["escape: orphan `escape` statement","escape: orphan `escape` statement", "trap: missing `escape` statement","escape: unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkStmtsIt (Error () "")               []
    checkStmtsIt (Write () "x" (Const () 0)) []

    -- compound statements --
    checkStmtsIt (Seq () (Escape () 1) (Escape () 0)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Trap () (Escape () 1))) (Escape () 0)) ["trap: missing `escape` statement"]
    checkStmtsIt (Seq () (Escape () 0) (Escape () 1)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (AwaitInp () "FOREVER") (Escape () 1)) ["escape: unreachable statement"]
    checkStmtsIt (Seq () (Seq () (AwaitInp () "FOREVER") (Nop ())) (Escape () 1)) ["nop: unreachable statement",("escape: unreachable statement")]
    checkStmtsIt (Seq () (Loop () (Nop ())) (Nop ())) ["loop: unbounded `loop` execution","nop: unreachable statement"]
    checkStmtsIt (Seq () (Every () "" (Nop ())) (Nop ())) ["nop: unreachable statement"]
    checkStmtsIt (Seq () (Par () (Nop ()) (Every () "" (Nop ()))) (Nop ())) ["parallel: terminating trail","nop: unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Escape () 1))))) (Nop ())) ["escape: unreachable statement","loop: unbounded `loop` execution"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["trap: missing `escape` statement","nop: unreachable statement", "loop: unbounded `loop` execution","nop: unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkId -- declarations" $ do

    checkIdIt (Nop ())                                 []
    checkIdIt (Var () "a" (Nop ()))                    []
    checkIdIt (Var () "a" (Write () "a" (Const () 1))) []
    checkIdIt (Var () "a" (Var () "a" (Nop ())))       ["declaration: identifier 'a' is already declared"]
    checkIdIt (Evt () "e" (Evt () "e" (Nop ())))       ["declaration: identifier 'e' is already declared"]
    checkIdIt (Write () "a" (Const () 1))              ["assignment: identifier 'a' is not declared"]
    checkIdIt (AwaitEvt () "e")                        ["await: identifier 'e' is not declared"]
    checkIdIt (Every () "e" (Nop ()))                  ["every: identifier 'e' is not declared"]
    checkIdIt (Pause () "a" (Nop ()))                  ["pause/if: identifier 'a' is not declared"]
    checkIdIt (Var () "a" (Write () "a" (Umn () (Read () "b")))) ["read access to 'b': identifier 'b' is not declared"]

  --------------------------------------------------------------------------
  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Write () "c" (Const () 0)) []
    checkStmtsIt (AwaitInp () "A")        []
    checkStmtsIt (AwaitEvt () "a")        []
    checkStmtsIt (EmitEvt () "a")         []
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
    checkStmtsIt (Par () (Escape () 0) (AwaitInp () "FOREVER")) []
    checkStmtsIt (Par () (AwaitInp () "FOREVER") (Seq () (EmitEvt () "a") (AwaitInp () "FOREVER"))) []
    checkStmtsIt (Par () (Nop ()) (EmitEvt () "a"))    ["parallel: terminating trail"]
    checkStmtsIt (Pause () "a" (Nop ()))               []
    checkStmtsIt (Fin () (Nop ()))                     []
    checkStmtsIt (Fin () (Fin () (Nop ())))            ["finalize: invalid statement in `finalize`", "finalize: invalid statement"]

    -- misc --
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Escape () 0)))) ["loop: `loop` never iterates","finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Nop ())))) ["loop: unbounded `loop` execution"]
    checkStmtsIt (Var () "x" (Fin () (Every () "A" (Nop ())))) ["finalize: invalid statement in `finalize`", "every: invalid statement"]
    checkStmtsIt (Loop () (Trap () (Loop () (Escape () 0))))   ["loop: `loop` never iterates","loop: unbounded `loop` execution"]
    checkStmtsIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) ["escape: unreachable statement","loop: `loop` never iterates","loop: unbounded `loop` execution"]
    checkStmtsIt (AwaitEvt () "a" `sSeq` (Fin () (Escape () 0)) `sPar` (AwaitInp () "FOREVER")) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (AwaitEvt () "a" `sSeq` (Every () "A" (Fin () (Nop ()))) `sPar` (AwaitInp () "FOREVER")) ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Loop () ((AwaitInp () "FOREVER") `sPar` Loop () (Loop () (Loop () (AwaitInp () "A")))))  ["loop: `loop` never iterates","loop: `loop` never iterates","loop: `loop` never iterates"]
    checkStmtsIt (Loop () ((Escape () 0) `sPar` Loop () (Loop () (Loop () (AwaitInp () "A"))))) ["loop: `loop` never iterates","loop: `loop` never iterates","loop: `loop` never iterates"]
    checkStmtsIt (Fin () (Escape () 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Loop () (AwaitInp () "FOREVER")) ["loop: `loop` never iterates"]

    -- all
    checkCheckIt (Fin () (Escape () 0)) ["escape: orphan `escape` statement", "finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Trap () (Fin () (Escape () 0))) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["trap: missing `escape` statement", "nop: unreachable statement", "loop: unbounded `loop` execution", "nop: unreachable statement"]
    checkCheckIt (Inp () "FOREVER" (Trap () (Seq () (Trap () (Par () (AwaitInp () "FOREVER") (Escape () 0))) (Escape () 0))))
      []
    checkCheckIt (Trap () (Par () (Escape () 0) (Seq () (Par () (Inp () "FOREVER" (AwaitInp () "FOREVER")) (Fin () (Nop ()))) (Escape () 0))))
      ["escape: unreachable statement"]

    describe "ext:" $ do
        it "emit O" $
            (fst $ Check.compile (False,False) (EmitExt () "O" Nothing))
            `shouldBe` ["emit: identifier 'O' is not declared"]
        it "out O; emit O" $
            Check.compile (False,False) (Out () "O" (EmitExt () "O" Nothing))
            `shouldBe` ([],Out () "O" (EmitExt () "O" Nothing))

        it "await I" $
            (fst $ Check.compile (False,False) (AwaitInp () "I"))
            `shouldBe` ["await: identifier 'I' is not declared"]
        it "inp I; await I" $
            Check.compile (False,False) (Inp () "I" (AwaitInp () "I"))
            `shouldBe` ([], (Inp () "I" (AwaitInp () "I")))

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
        checkIdIt p b    = checkIt' Id.check p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt :: Stmt () -> Errors -> Spec
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False))) p b
