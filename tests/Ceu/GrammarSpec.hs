module Ceu.GrammarSpec (main, spec) where

import Ceu.Globals
import Ceu.Grammar
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
    checkFinIt (Fin (Var "x" Nop))                                True
    checkFinIt (Fin (Var "x" (Every "A" Nop)))                    False
    checkFinIt (Fin (If (Const 0) (Loop (Escape 0)) (Nop)))       False
    checkFinIt (Fin (If (Const 0) (Write "x" (Const 0)) (Nop)))   True
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (AwaitExt "A") `Seq` Nop)) False
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (EmitInt "a") `Seq` Nop)) True
    checkFinIt (Fin (Loop (AwaitInt "a")))                        False
    checkFinIt (Fin (Loop (AwaitExt "A")))                        False
    checkFinIt (Fin (Nop `Par` Nop `Par` (EmitInt "a")))          True

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkEscapeIt (Error "")            True
    checkEscapeIt (Escape 0)            False
    checkEscapeIt (Write "x" (Const 0)) True

    -- compound statements --
    checkEscapeIt (Trap (Escape 0))                  True
    checkEscapeIt (Trap (Escape 1))                  False
    checkEscapeIt (Trap (Seq (Escape 0) (Escape 1))) False

  --------------------------------------------------------------------------
  describe "checkProg -- program is valid" $ do

    -- atomic statements --
    checkProgIt (Write "c" (Const 0)) True
    checkProgIt (AwaitExt "A")        True
    checkProgIt (AwaitInt "a")        True
    checkProgIt (EmitInt "a")         True
    checkProgIt (Escape 0)               True
    checkProgIt (Nop)                 True
    checkProgIt (Error "")            True

    -- compound statements --
    checkProgIt (Var "x" Nop)          True
    checkProgIt (If (Const 0) Nop (Escape 0)) True
    checkProgIt (Seq (Escape 0) Nop)          True
    checkProgIt (Loop (Escape 0))             True
    checkProgIt (Loop Nop)               False
    checkProgIt (Every "A" Nop)          True
    checkProgIt (Every "A" (Fin Nop))    False
    checkProgIt (Par (Escape 0) Nop)          True
    checkProgIt (Par Nop (EmitInt "a"))   True
    checkProgIt (Pause "a" Nop)          True
    checkProgIt (Fin Nop)                True
    checkProgIt (Fin (Fin Nop))          False

    -- misc --
    checkProgIt (Nop `Seq` (Fin (Loop (Escape 0))))                   False
    checkProgIt (Nop `Seq` (Fin (Loop Nop)))                          False
    checkProgIt (Var "x" (Fin (Every "A" Nop)))                       False
    checkProgIt (Loop (Trap (Loop (Escape 0))))                       False
    checkProgIt (Loop (Trap (Loop (Seq (Escape 0) (Escape 0)))))      False
    checkProgIt (AwaitInt "a" `Seq` (Fin (Escape 0)) `Par` Nop)       False
    checkProgIt (AwaitInt "a" `Seq` (Every "A" (Fin Nop)) `Par` Nop)  False
    checkProgIt (Loop (Nop `Par` Loop (Loop (Loop (AwaitExt "A")))))  False
    checkProgIt (Loop ((Escape 0) `Par` Loop (Loop (Loop (AwaitExt "A"))))) True

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b  = checkIt checkLoop p b
        checkFinIt p b   = checkIt checkFin p b
        checkEveryIt p b = checkIt checkEvery p b
        checkEscapeIt p b = checkIt checkEscape p b
        checkProgIt p b  = checkIt checkProg p b
