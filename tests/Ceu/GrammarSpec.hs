module Ceu.GrammarSpec (main, spec) where

import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import qualified Ceu.Grammar.Check.Check     as Check
import qualified Ceu.Grammar.Check.Escape    as Escape
import qualified Ceu.Grammar.Check.Loop      as Loop
import qualified Ceu.Grammar.Check.Reachable as Reachable
import qualified Ceu.Grammar.Check.VarEvt    as VarEvt
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "checkLoop -- matching-Break/Stmt$AwaitExt/Stmt$Every in all paths" $ do

    -- atomic statements --
    checkLoopIt (Stmt$Loop (Stmt$Write "x" (Exp$Umn (Exp$Const 1)))) False
    checkLoopIt (Stmt$Loop (Stmt$AwaitExt "A"))              True
    checkLoopIt (Stmt$Loop (Stmt$AwaitInt "a"))              False
    checkLoopIt (Stmt$Loop (Stmt$EmitInt "a"))               False
    checkLoopIt (Stmt$Loop (Stmt$Escape 0))                  True
    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$Escape 0)))           True
    checkLoopIt (Stmt$Loop ((Stmt Nop)))                       False
    checkLoopIt (Stmt$Loop (Stmt$Error ""))                  False

    -- compound statements --
    checkLoopIt (Stmt$Loop (Stmt$Var "x" (Stmt$Var "y" (Stmt$Escape 0))))            True
    checkLoopIt (Stmt$Loop (Stmt$Var "x" (Stmt$Var "y" (Stmt Nop))))                   False

    checkLoopIt (Stmt$Loop (Stmt$If (Exp$Const 0) (Stmt$Escape 0) (Stmt Nop)))         False
    checkLoopIt (Stmt$Loop (Stmt$If (Exp$Const 0) (Stmt$Fin (Stmt Nop)) (Stmt Nop)))          False
    checkLoopIt (Stmt$Loop (Stmt$If (Exp$Const 0) (Stmt$Every "A" (Stmt Nop)) (Stmt$AwaitExt "A"))) True

{-
    checkLoopIt (Stmt$Loop ((Stmt Nop) `Stmt$Seq` (Stmt Nop) `Stmt$Seq` (Stmt$Escape 0) `Stmt$Seq` (Stmt Nop))) True
    checkLoopIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Escape 0))))                  False
    checkLoopIt (Stmt$Loop ((Stmt Nop) `Stmt$Seq` (Stmt Nop) `Stmt$Seq` (Stmt$Loop (Stmt$Escape 0))))   True
    checkLoopIt (Stmt$Loop ((Stmt$Escape 0) `Stmt$Seq` Stmt$Loop (Stmt Nop)))               True
    checkLoopIt (Stmt$Loop ((Stmt Nop) `Stmt$Seq` Stmt$Loop (Stmt Nop)))                      False
-}

    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$Loop (Stmt$AwaitExt "A"))))              True
    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$Escape 0)))                         True
    checkLoopIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Escape 0))))                  False
    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Escape 0)))))           False
{-
    checkLoopIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Escape 0)) `Stmt$Seq` (Stmt$Trap (Stmt$Loop (Stmt$Escape 0))))) False
    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$AwaitExt "A") `Stmt$Seq` Stmt$Loop (Stmt Nop)))      True
-}
    checkLoopIt (Stmt$Loop (Stmt$Loop (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 0))))        True
    checkLoopIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 0))))) False
    checkLoopIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 1))))) False

{-
    checkLoopIt (Stmt$Loop ((Stmt Nop) `Stmt$Par` (Stmt Nop) `Stmt$Par` (Stmt Nop)))                 False
    checkLoopIt (Stmt$Loop (Stmt$Pause "a" (Stmt Nop)))                           False
    checkLoopIt (Stmt$Loop (Stmt$Every "A" (Stmt Nop) `Stmt$Par` Stmt$AwaitExt "A" `Stmt$Par` (Stmt$Escape 0))) True
-}
    checkLoopIt (Stmt$Loop (Stmt$Pause "a" (Stmt$AwaitExt "A")))                True

    -- Stmt$Fin always run in zero time.
    checkLoopIt (Stmt$Loop (Stmt$Fin (Stmt Nop)))                                 False
    checkLoopIt (Stmt$Loop (Stmt$Fin (Stmt$Escape 0)))                          False
    checkLoopIt (Stmt$Loop (Stmt$Fin (Stmt$AwaitExt "A")))                      False
    checkLoopIt (Stmt$Loop (Stmt$Fin (Stmt$Every "A" (Stmt Nop))))                     False

  --------------------------------------------------------------------------
  describe "checkFin/Stmt$Every -- no Stmt$Loop/Stmt$Escape/Await*/Stmt$Every/Stmt$Fin:" $ do

    -- atomic statements --
    checkFinIt (Stmt$Fin (Stmt$Write "x" (Exp$Const 0))) []
    checkFinIt (Stmt$Fin (Stmt$AwaitExt "A"))        ["await: invalid statement"]
    checkFinIt (Stmt$Fin (Stmt$AwaitInt "a"))        ["await: invalid statement"]
    checkFinIt (Stmt$Fin (Stmt$EmitInt "a"))         []
    checkFinIt (Stmt$Fin (Stmt$Escape 0))            ["escape: invalid statement"]
    checkFinIt (Stmt$Fin ((Stmt Nop)))                 []
    checkFinIt (Stmt$Fin (Stmt$Error ""))            []

    -- compound statements --
    checkFinIt (Stmt$Fin (Stmt$Var "x" (Stmt Nop)))                                  []
    checkFinIt (Stmt$Fin (Stmt$Var "x" (Stmt$Every "A" (Stmt Nop))))                      ["every: invalid statement"]
    checkFinIt (Stmt$Fin (Stmt$If (Exp$Const 0) (Stmt$Loop (Stmt$Escape 0)) ((Stmt Nop))))     ["escape: invalid statement"]
    checkFinIt (Stmt$Fin (Stmt$If (Exp$Const 0) (Stmt$Write "x" (Exp$Const 0)) ((Stmt Nop)))) []
{-
    checkFinIt (Stmt$Fin ((Stmt Nop) `Stmt$Seq` (Stmt Nop) `Stmt$Seq` (Stmt$AwaitExt "A") `Stmt$Seq` (Stmt Nop))) ["await: invalid statement"]
    checkFinIt (Stmt$Fin ((Stmt Nop) `Stmt$Seq` (Stmt Nop) `Stmt$Seq` (Stmt$EmitInt "a") `Stmt$Seq` (Stmt Nop)))  []
-}
    checkFinIt (Stmt$Fin (Stmt$Loop (Stmt$AwaitInt "a")))                          ["await: invalid statement"]
    checkFinIt (Stmt$Fin (Stmt$Loop (Stmt$AwaitExt "A")))                          ["await: invalid statement"]
{-
    checkFinIt (Stmt$Fin ((Stmt Nop) `Stmt$Par` (Stmt Nop) `Stmt$Par` (Stmt$EmitInt "a")))            ["parallel: invalid statement","parallel: invalid statement"]
-}

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkEscapeIt (Stmt$Error "")                []
    checkEscapeIt (Stmt$Escape 0)                ["escape: orphan `escape` statement"]
    checkEscapeIt (Stmt$Write "x" (Exp$Const 0)) []

    -- compound statements --
    checkEscapeIt (Stmt$Trap (Stmt$Escape 0))                  []
    checkEscapeIt (Stmt$Trap (Stmt$Escape 1))                  ["trap: missing `escape` statement","escape: orphan `escape` statement"]
    checkEscapeIt (Stmt$Trap (Stmt$Trap (Stmt$Escape 0)))           ["trap: missing `escape` statement"]
    checkEscapeIt (Stmt$Trap (Stmt$Trap (Stmt$Escape 1)))           ["trap: missing `escape` statement"]
    checkEscapeIt (Stmt$Trap (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 1))) ["escape: orphan `escape` statement"]
    checkEscapeIt (Stmt$Trap (Stmt$Seq (Stmt$Escape 1) (Stmt$Escape 1))) ["trap: missing `escape` statement","escape: orphan `escape` statement", "escape: orphan `escape` statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkReachableIt (Stmt$Error "")                []
    checkReachableIt (Stmt$Write "x" (Exp$Const 0)) []

    -- compound statements --
    checkReachableIt (Stmt$Seq (Stmt$Escape 1) (Stmt$Escape 0)) ["escape: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Trap (Stmt$Trap (Stmt$Escape 1))) (Stmt$Escape 0)) []
    checkReachableIt (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 1)) ["escape: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$AwaitExt "FOREVER") (Stmt$Escape 1)) ["escape: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Seq (Stmt$AwaitExt "FOREVER") (Stmt Nop)) (Stmt$Escape 1)) ["nop: unreachable statement",("escape: unreachable statement")]
    checkReachableIt (Stmt$Seq (Stmt$Loop (Stmt Nop)) (Stmt Nop)) ["nop: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Every "" (Stmt Nop)) (Stmt Nop)) ["nop: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Par (Stmt Nop) (Stmt$Every "" (Stmt Nop))) (Stmt Nop)) ["nop: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Trap (Stmt$Loop (Stmt$Trap (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 1))))) (Stmt Nop)) ["escape: unreachable statement"]
    checkReachableIt (Stmt$Seq (Stmt$Trap (Stmt$Loop (Stmt$Trap (Stmt$Seq (Stmt$Escape 0) (Stmt Nop))))) (Stmt Nop)) ["nop: unreachable statement", "nop: unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkVarEvt -- declarations" $ do

    checkVarEvtIt (Stmt Nop)                                 []
    checkVarEvtIt (Stmt$Var "a" (Stmt Nop))                       []
    checkVarEvtIt (Stmt$Var "a" (Stmt$Write "a" (Exp$Const 1))) []
    checkVarEvtIt (Stmt$Var "a" (Stmt$Var "a" (Stmt Nop)))             ["declaration: variable 'a' is already declared"]
    checkVarEvtIt (Stmt$Int "e" (Stmt$Int "e" (Stmt Nop)))       ["declaration: event 'e' is already declared"]
    checkVarEvtIt (Stmt$Write "a" (Exp$Const 1))     ["assignment: variable 'a' is not declared"]
    checkVarEvtIt (Stmt$AwaitInt "e")                ["await: event 'e' is not declared"]
    checkVarEvtIt (Stmt$Every "e" (Stmt Nop))               ["every: event 'e' is not declared"]
    checkVarEvtIt (Stmt$Pause "a" (Stmt Nop))               ["pause/if: variable 'a' is not declared"]
    checkVarEvtIt (Stmt$Var "a" (Stmt$Write "a" (Exp$Umn (Exp$Read "b")))) ["read access to 'b': variable 'b' is not declared"]

  --------------------------------------------------------------------------
  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Stmt$Write "c" (Exp$Const 0)) []
    checkStmtsIt (Stmt$AwaitExt "A")        []
    checkStmtsIt (Stmt$AwaitInt "a")        []
    checkStmtsIt (Stmt$EmitInt "a")         []
    checkStmtsIt (Stmt$Escape 0)            []
    checkStmtsIt ((Stmt Nop))                 []
    checkStmtsIt (Stmt$Error "")            []

    -- compound statements --
    checkStmtsIt (Stmt$Var "x" (Stmt Nop))                   []
    checkStmtsIt (Stmt$If (Exp$Const 0) (Stmt Nop) (Stmt$Escape 0)) []
    checkStmtsIt (Stmt$Seq (Stmt$Escape 0) (Stmt Nop))            []
    checkStmtsIt (Stmt$Loop (Stmt$Escape 0))               []
    checkStmtsIt (Stmt$Loop (Stmt Nop))                      ["loop: unbounded `loop` execution"]
    checkStmtsIt (Stmt$Every "A" (Stmt Nop))                 []
    checkStmtsIt (Stmt$Every "A" (Stmt$Fin (Stmt Nop)))           ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Stmt$Par (Stmt$Escape 0) (Stmt Nop))            ["parallel: terminating trail"]
    checkStmtsIt (Stmt$Par (Stmt$Escape 0) (Stmt$AwaitExt "FOREVER"))
                                                 []
    checkStmtsIt (Stmt$Par (Stmt$AwaitExt "FOREVER") (Stmt$Seq (Stmt$EmitInt "a") (Stmt$AwaitExt "FOREVER")))
                                                 []
    checkStmtsIt (Stmt$Par (Stmt Nop) (Stmt$EmitInt "a"))         ["parallel: terminating trail"]
    checkStmtsIt (Stmt$Pause "a" (Stmt Nop))                 []
    checkStmtsIt (Stmt$Fin (Stmt Nop))                       []
    checkStmtsIt (Stmt$Fin (Stmt$Fin (Stmt Nop)))                 ["finalize: invalid statement in `finalize`", "finalize: invalid statement"]

    -- misc --
{-
    checkStmtsIt ((Stmt Nop) `Stmt$Seq` (Stmt$Fin (Stmt$Loop (Stmt$Escape 0)))) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt ((Stmt Nop) `Stmt$Seq` (Stmt$Fin (Stmt$Loop (Stmt Nop))))        ["loop: unbounded `loop` execution"]
-}
    checkStmtsIt (Stmt$Var "x" (Stmt$Fin (Stmt$Every "A" (Stmt Nop))))     ["finalize: invalid statement in `finalize`", "every: invalid statement"]
    checkStmtsIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Escape 0))))     ["loop: unbounded `loop` execution"]
    checkStmtsIt (Stmt$Loop (Stmt$Trap (Stmt$Loop (Stmt$Seq (Stmt$Escape 0) (Stmt$Escape 0)))))
                                                     ["loop: unbounded `loop` execution"]
{-
    checkStmtsIt (Stmt$AwaitInt "a" `Stmt$Seq` (Stmt$Fin (Stmt$Escape 0)) `Stmt$Par` (Stmt$AwaitExt "FOREVER"))
                                                     ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Stmt$AwaitInt "a" `Stmt$Seq` (Stmt$Every "A" (Stmt$Fin (Stmt Nop))) `Stmt$Par` (Stmt$AwaitExt "FOREVER"))
                                                     ["every: invalid statement in `every`", "finalize: invalid statement"]
    checkStmtsIt (Stmt$Loop ((Stmt$AwaitExt "FOREVER") `Stmt$Par` Stmt$Loop (Stmt$Loop (Stmt$Loop (Stmt$AwaitExt "A")))))  []
    checkStmtsIt (Stmt$Loop ((Stmt$Escape 0) `Stmt$Par` Stmt$Loop (Stmt$Loop (Stmt$Loop (Stmt$AwaitExt "A"))))) []
-}
    checkStmtsIt (Stmt$Fin (Stmt$Escape 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkStmtsIt (Stmt$Loop (Stmt$Escape 0)) []
    checkStmtsIt (Stmt$Loop (Stmt$AwaitExt "FOREVER")) []

    -- all
    checkCheckIt (Stmt$Fin (Stmt$Escape 0)) ["finalize: invalid statement in `finalize`", "escape: invalid statement", "escape: orphan `escape` statement"]
    checkCheckIt (Stmt$Trap (Stmt$Fin (Stmt$Escape 0))) ["finalize: invalid statement in `finalize`", "escape: invalid statement"]
    checkCheckIt (Stmt$Seq (Stmt$Trap (Stmt$Loop (Stmt$Trap (Stmt$Seq (Stmt$Escape 0) (Stmt Nop))))) (Stmt Nop)) ["loop: unbounded `loop` execution", "trap: missing `escape` statement", "nop: unreachable statement", "nop: unreachable statement"]
    checkCheckIt (Stmt$Trap (Stmt$Seq (Stmt$Trap (Stmt$Par (Stmt$AwaitExt "FOREVER") (Stmt$Escape 0))) (Stmt$Escape 0)))
      []
    checkCheckIt (Stmt$Trap (Stmt$Par (Stmt$Escape 0) (Stmt$Seq (Stmt$Par (Stmt$AwaitExt "FOREVER") (Stmt$Fin (Stmt Nop))) (Stmt$Escape 0))))
      ["escape: unreachable statement"]

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt  Loop.check p b
        checkFinIt (Stmt (Fin p)) b = checkIt' Check.getTights p b
        checkEveryIt p b     = checkIt' Check.getTights p b
        checkEscapeIt p b    = checkIt' Escape.check p b
        checkReachableIt p b = checkIt' Reachable.check p b
        checkVarEvtIt p b    = checkIt' VarEvt.check p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False))) p b
