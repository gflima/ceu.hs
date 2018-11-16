module Ceu.GrammarSpec (main, spec) where

import Ceu.Globals
import Ceu.Grammar
import qualified Ceu.Grammar.Check        as Check
import qualified Ceu.Grammar.Check.Escape as Escape
import qualified Ceu.Grammar.Check.Loop   as Loop
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
    checkFinIt (Fin (Write "x" (Const 0))) True
    checkFinIt (Fin (AwaitExt "A"))        False
    checkFinIt (Fin (AwaitInt "a"))        False
    checkFinIt (Fin (EmitInt "a"))         True
    checkFinIt (Fin (Escape 0))               False
    checkFinIt (Fin (Nop))                 True
    checkFinIt (Fin (Error ""))            True

    -- compound statements --
    checkFinIt (Fin (Var "x" Nop))                                  True
    checkFinIt (Fin (Var "x" (Every "A" Nop)))                      False
    checkFinIt (Fin (If (Const 0) (Loop (Escape 0)) (Nop)))         False
    checkFinIt (Fin (If (Const 0) (Write "x" (Const 0)) (Nop)))     True
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (AwaitExt "A") `Seq` Nop)) False
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (EmitInt "a") `Seq` Nop))  True
    checkFinIt (Fin (Loop (AwaitInt "a")))                          False
    checkFinIt (Fin (Loop (AwaitExt "A")))                          False
    checkFinIt (Fin (Nop `Par` Nop `Par` (EmitInt "a")))            False

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkEscapeIt (Error "")            []
    checkEscapeIt (Escape 0)            [("orphan `escape` statement", Escape 0)]
    checkEscapeIt (Write "x" (Const 0)) []

    -- compound statements --
    checkEscapeIt (Trap (Escape 0))                  []
    checkEscapeIt (Trap (Escape 1))                  [("orphan `escape` statement", Escape 1)]
    checkEscapeIt (Trap (Seq (Escape 0) (Escape 1))) [("orphan `escape` statement", Escape 1)]
    checkEscapeIt (Trap (Seq (Escape 1) (Escape 1))) [("orphan `escape` statement", Escape 1),("orphan `escape` statement", Escape 1)]

  --------------------------------------------------------------------------
  describe "checkProg -- program is valid" $ do

    -- atomic statements --
    checkProgIt (Write "c" (Const 0)) []
    checkProgIt (AwaitExt "A")        []
    checkProgIt (AwaitInt "a")        []
    checkProgIt (EmitInt "a")         []
    checkProgIt (Escape 0)            []
    checkProgIt (Nop)                 []
    checkProgIt (Error "")            []

    -- compound statements --
    checkProgIt (Var "x" Nop)                   []
    checkProgIt (If (Const 0) Nop (Escape 0))   []
    checkProgIt (Seq (Escape 0) Nop)            []
    checkProgIt (Loop (Escape 0))               []
    checkProgIt (Loop Nop)                      [("unbounded `loop` execution", Loop Nop)]
    checkProgIt (Every "A" Nop)                 []
    checkProgIt (Every "A" (Fin Nop))           [("invalid statement in `every`", Every "A" (Fin Nop))]
    checkProgIt (Par (Escape 0) Nop)            []
    checkProgIt (Par Nop (EmitInt "a"))         []
    checkProgIt (Pause "a" Nop)                 []
    checkProgIt (Fin Nop)                       []
    checkProgIt (Fin (Fin Nop))                 [("invalid statement in `finalize`", Fin (Fin Nop))]

    -- misc --
    checkProgIt (Nop `Seq` (Fin (Loop (Escape 0))))                   [("invalid statement in `finalize`", Fin (Loop (Escape 0)))]
    checkProgIt (Nop `Seq` (Fin (Loop Nop)))                          [("unbounded `loop` execution", Loop Nop),("invalid statement in `finalize`", Fin (Loop Nop))]
    checkProgIt (Var "x" (Fin (Every "A" Nop)))                       [("invalid statement in `finalize`", Fin (Every "A" Nop))]
    checkProgIt (Loop (Trap (Loop (Escape 0))))                       [("unbounded `loop` execution", Loop (Trap (Loop (Escape 0))))]
    checkProgIt (Loop (Trap (Loop (Seq (Escape 0) (Escape 0)))))      [("unbounded `loop` execution", Loop (Trap (Loop (Seq (Escape 0) (Escape 0)))))]
    checkProgIt (AwaitInt "a" `Seq` (Fin (Escape 0)) `Par` Nop)       [("invalid statement in `finalize`", Fin (Escape 0))]
    checkProgIt (AwaitInt "a" `Seq` (Every "A" (Fin Nop)) `Par` Nop)  [("invalid statement in `every`", Every "A" (Fin Nop))]
    checkProgIt (Loop (Nop `Par` Loop (Loop (Loop (AwaitExt "A")))))  []
    checkProgIt (Loop ((Escape 0) `Par` Loop (Loop (Loop (AwaitExt "A"))))) []

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt Loop.check p b
        checkFinIt (Fin p) b = checkIt Check.tight p b
        checkEveryIt p b     = checkIt Check.tight p b
        checkEscapeIt p b    = checkIt' Escape.check p b
        checkProgIt p b      = checkIt' Check.stmts p b
