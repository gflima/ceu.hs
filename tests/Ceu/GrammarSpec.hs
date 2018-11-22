module Ceu.GrammarSpec (main, spec) where

import Ceu.Globals
import Ceu.Grammar
import qualified Ceu.Grammar.Check           as Check
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Reachable as Reachable
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "checkLoop -- matching-Break/AwaitExt/Every in all paths" $ do

    -- atomic statements --
    checkLoopIt (Loop (Write "x" (Umn (Const 1)))) False
    checkLoopIt (Loop (AwaitExt "A"))              True
    checkLoopIt (Loop (AwaitInt "a"))              False
    checkLoopIt (Loop (EmitInt "a"))               False
    checkLoopIt (Loop (Escape 0))                  True
    checkLoopIt (Loop (Loop (Escape 0)))           True
    checkLoopIt (Loop (Nop))                       False
    checkLoopIt (Loop (Error ""))                  False

    -- compound statements --
    checkLoopIt (Loop (Var "x" (Var "y" (Escape 0))))            True
    checkLoopIt (Loop (Var "x" (Var "y" Nop)))                   False

    checkLoopIt (Loop (If (Const 0) (Escape 0) Nop))             False
    checkLoopIt (Loop (If (Const 0) (Fin Nop) Nop))              False
    checkLoopIt (Loop (If (Const 0) (Every "A" Nop) (AwaitExt "A"))) True

    checkLoopIt (Loop (Nop `Seq` Nop `Seq` (Escape 0) `Seq` Nop)) True
    checkLoopIt (Loop (Trap (Loop (Escape 0))))                  False
    checkLoopIt (Loop (Nop `Seq` Nop `Seq` (Loop (Escape 0))))   True
    checkLoopIt (Loop ((Escape 0) `Seq` Loop Nop))               True
    checkLoopIt (Loop (Nop `Seq` Loop Nop))                      False

    checkLoopIt (Loop (Loop (Loop (AwaitExt "A"))))              True
    checkLoopIt (Loop (Loop (Escape 0)))                         True
    checkLoopIt (Loop (Trap (Loop (Escape 0))))                  False
    checkLoopIt (Loop (Loop (Trap (Loop (Escape 0)))))           False
    checkLoopIt (Loop (Trap (Loop (Escape 0)) `Seq` (Trap (Loop (Escape 0))))) False
    checkLoopIt (Loop (Loop (AwaitExt "A") `Seq` Loop Nop))      True
    checkLoopIt (Loop (Loop (Seq (Escape 0) (Escape 0))))        True
    checkLoopIt (Loop (Trap (Loop (Seq (Escape 0) (Escape 0))))) False
    checkLoopIt (Loop (Trap (Loop (Seq (Escape 0) (Escape 1))))) False

    checkLoopIt (Loop (Nop `Par` Nop `Par` Nop))                 False
    checkLoopIt (Loop (Pause "a" Nop))                           False
    checkLoopIt (Loop (Every "A" Nop `Par` AwaitExt "A" `Par` (Escape 0))) True
    checkLoopIt (Loop (Pause "a" (AwaitExt "A")))                True

    -- Fin always run in zero time.
    checkLoopIt (Loop (Fin Nop))                                 False
    checkLoopIt (Loop (Fin (Escape 0)))                          False
    checkLoopIt (Loop (Fin (AwaitExt "A")))                      False
    checkLoopIt (Loop (Fin (Every "A" Nop)))                     False

  --------------------------------------------------------------------------
  describe "checkFin/Every -- no Loop/Escape/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin (Write "x" (Const 0))) []
    checkFinIt (Fin (AwaitExt "A"))        ["await: invalid statement"]
    checkFinIt (Fin (AwaitInt "a"))        ["await: invalid statement"]
    checkFinIt (Fin (EmitInt "a"))         []
    checkFinIt (Fin (Escape 0))            ["escape: invalid statement"]
    checkFinIt (Fin (Nop))                 []
    checkFinIt (Fin (Error ""))            []

    -- compound statements --
    checkFinIt (Fin (Var "x" Nop))                                  []
    checkFinIt (Fin (Var "x" (Every "A" Nop)))                      ["every: invalid statement"]
    checkFinIt (Fin (If (Const 0) (Loop (Escape 0)) (Nop)))         ["escape: invalid statement"]
    checkFinIt (Fin (If (Const 0) (Write "x" (Const 0)) (Nop)))     []
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (AwaitExt "A") `Seq` Nop)) ["await: invalid statement"]
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (EmitInt "a") `Seq` Nop))  []
    checkFinIt (Fin (Loop (AwaitInt "a")))                          ["await: invalid statement"]
    checkFinIt (Fin (Loop (AwaitExt "A")))                          ["await: invalid statement"]
    checkFinIt (Fin (Nop `Par` Nop `Par` (EmitInt "a")))            ["parallel: invalid statement","parallel: invalid statement"]

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkEscapeIt (Error "")            []
    checkEscapeIt (Escape 0)            ["escape: orphan `escape` statement"]
    checkEscapeIt (Write "x" (Const 0)) []

    -- compound statements --
    checkEscapeIt (Trap (Escape 0))                  []
    checkEscapeIt (Trap (Escape 1))                  ["trap: missing `escape` statement","escape: orphan `escape` statement"]
    checkEscapeIt (Trap (Trap (Escape 0)))           ["trap: missing `escape` statement"]
    checkEscapeIt (Trap (Trap (Escape 1)))           ["trap: missing `escape` statement"]
    checkEscapeIt (Trap (Seq (Escape 0) (Escape 1))) ["escape: orphan `escape` statement"]
    checkEscapeIt (Trap (Seq (Escape 1) (Escape 1))) ["trap: missing `escape` statement","escape: orphan `escape` statement", "escape: orphan `escape` statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkReachableIt (Error "")            []
    checkReachableIt (Write "x" (Const 0)) []

    -- compound statements --
    checkReachableIt (Seq (Escape 1) (Escape 0)) ["escape: unreachable statement"]
    checkReachableIt (Seq (Trap (Trap (Escape 1))) (Escape 0)) []
    checkReachableIt (Seq (Escape 0) (Escape 1)) ["escape: unreachable statement"]
    checkReachableIt (Seq (AwaitExt "FOREVER") (Escape 1)) ["escape: unreachable statement"]
    checkReachableIt (Seq (Seq (AwaitExt "FOREVER") Nop) (Escape 1)) ["nop: unreachable statement",("escape: unreachable statement")]
    checkReachableIt (Seq (Loop Nop) Nop) ["nop: unreachable statement"]
    checkReachableIt (Seq (Every "" Nop) Nop) ["nop: unreachable statement"]
    checkReachableIt (Seq (Par Nop (Every "" Nop)) Nop) ["nop: unreachable statement"]
    checkReachableIt (Seq (Trap (Loop (Trap (Seq (Escape 0) (Escape 1))))) Nop) ["escape: unreachable statement"]
    checkReachableIt (Seq (Trap (Loop (Trap (Seq (Escape 0) Nop)))) Nop) ["nop: unreachable statement", "nop: unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Write "c" (Const 0)) []
    checkStmtsIt (AwaitExt "A")        []
    checkStmtsIt (AwaitInt "a")        []
    checkStmtsIt (EmitInt "a")         []
    checkStmtsIt (Escape 0)            []
    checkStmtsIt (Nop)                 []
    checkStmtsIt (Error "")            []

    -- compound statements --
    checkStmtsIt (Var "x" Nop)                   []
    checkStmtsIt (If (Const 0) Nop (Escape 0))   []
    checkStmtsIt (Seq (Escape 0) Nop)            []
    checkStmtsIt (Loop (Escape 0))               []
    checkStmtsIt (Loop Nop)                      ["loop: unbounded `loop` execution"]
    checkStmtsIt (Every "A" Nop)                 []
    checkStmtsIt (Every "A" (Fin Nop))           ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Par (Escape 0) Nop)            []
    checkStmtsIt (Par Nop (EmitInt "a"))         []
    checkStmtsIt (Pause "a" Nop)                 []
    checkStmtsIt (Fin Nop)                       []
    checkStmtsIt (Fin (Fin Nop))                 ["finalize: invalid statement in `finalize`", "finalize: invalid statement"]

    -- misc --
    checkStmtsIt (Nop `Seq` (Fin (Loop (Escape 0))))                   ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Nop `Seq` (Fin (Loop Nop)))                          ["loop: unbounded `loop` execution"]
    checkStmtsIt (Var "x" (Fin (Every "A" Nop)))                       ["finalize: invalid statement in `finalize`", "every: invalid statement"]
    checkStmtsIt (Loop (Trap (Loop (Escape 0))))                       ["loop: unbounded `loop` execution"]
    checkStmtsIt (Loop (Trap (Loop (Seq (Escape 0) (Escape 0)))))      ["loop: unbounded `loop` execution"]
    checkStmtsIt (AwaitInt "a" `Seq` (Fin (Escape 0)) `Par` Nop)       ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (AwaitInt "a" `Seq` (Every "A" (Fin Nop)) `Par` Nop)  ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Loop (Nop `Par` Loop (Loop (Loop (AwaitExt "A")))))  []
    checkStmtsIt (Loop ((Escape 0) `Par` Loop (Loop (Loop (AwaitExt "A"))))) []
    checkStmtsIt (Fin (Escape 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Loop (Escape 0)) []
    checkStmtsIt (Loop (AwaitExt "FOREVER")) []

    -- all
    checkCheckIt (Fin (Escape 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement", "escape: orphan `escape` statement"]
    checkCheckIt (Trap (Fin (Escape 0))) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Seq (Trap (Loop (Trap (Seq (Escape 0) Nop)))) Nop) ["loop: unbounded `loop` execution", "trap: missing `escape` statement", "nop: unreachable statement", "nop: unreachable statement"]
    checkCheckIt (Trap (Seq (Trap (Par (AwaitExt "FOREVER") (Escape 0))) (Escape 0)))
      []
    checkCheckIt (Trap (Par (Escape 0) (Seq (Par Nop (Fin Nop)) (Escape 0))))
      ["escape: unreachable statement"]

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt  Loop.check p b
        checkFinIt (Fin p) b = checkIt' Check.tight p b
        checkEveryIt p b     = checkIt' Check.tight p b
        checkEscapeIt p b    = checkIt' Escape.check p b
        checkReachableIt p b = checkIt' Reachable.check p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False))) p b
