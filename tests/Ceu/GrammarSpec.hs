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
    checkLoopIt (Loop (Break))                     True
    checkLoopIt (Loop (Nop))                       False
    checkLoopIt (Loop (Error ""))                  False

    -- compound statements --
    checkLoopIt (Loop (Var "x" (Var "y" Break)))                 True
    checkLoopIt (Loop (Var "x" (Var "y" Nop)))                   False

    checkLoopIt (Loop (If (Const 0) Break Nop))                  False
    checkLoopIt (Loop (If (Const 0) (Fin Nop) Nop))              False
    checkLoopIt (Loop (If (Const 0) (Every "A" Nop) (AwaitExt "A"))) True

    checkLoopIt (Loop (Nop `Seq` Nop `Seq` Break `Seq` Nop))     True
    checkLoopIt (Loop (Nop `Seq` Nop `Seq` (Loop Break)))        False
    checkLoopIt (Loop (Break `Seq` Loop Nop))                    True
    checkLoopIt (Loop (Nop `Seq` Loop Nop))                      False

    checkLoopIt (Loop (Loop (Loop (AwaitExt "A"))))              True
    checkLoopIt (Loop (Loop Break))                              False
    checkLoopIt (Loop (Loop (Loop Break)))                       False
    checkLoopIt (Loop (Loop Break `Seq` Loop Break))             False
    checkLoopIt (Loop (Loop (AwaitExt "A") `Seq` Loop Nop))      True
    checkLoopIt (Loop (Loop (Seq Break Break)))                  False

    checkLoopIt (Loop (Nop `And` Nop `And` Nop))                 False
    checkLoopIt (Loop (Nop `Or` Nop `Or` Nop))                   False
    checkLoopIt (Loop (Pause "a" Nop))                           False
    checkLoopIt (Loop (Every "A" Nop `Or` AwaitExt "A" `Or` Break)) True
    checkLoopIt (Loop (Pause "a" (AwaitExt "A")))                True

    -- Fin always run in zero time.
    checkLoopIt (Loop (Fin Nop))                                 False
    checkLoopIt (Loop (Fin Break))                               False
    checkLoopIt (Loop (Fin (AwaitExt "A")))                      False
    checkLoopIt (Loop (Fin (Every "A" Nop)))                     False

  --------------------------------------------------------------------------
  describe "checkFin/Every -- no Loop/Break/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin (Write "x" (Const 0))) True
    checkFinIt (Fin (AwaitExt "A"))        False
    checkFinIt (Fin (AwaitInt "a"))        False
    checkFinIt (Fin (EmitInt "a"))         True
    checkFinIt (Fin (Break))               False
    checkFinIt (Fin (Nop))                 True
    checkFinIt (Fin (Error ""))            True

    -- compound statements --
    checkFinIt (Fin (Var "x" Nop))                                True
    checkFinIt (Fin (Var "x" (Every "A" Nop)))                    False
    checkFinIt (Fin (If (Const 0) (Loop Break) (Nop)))            False
    checkFinIt (Fin (If (Const 0) (Write "x" (Const 0)) (Nop)))   True
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (AwaitExt "A") `Seq` Nop)) False
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (EmitInt "a") `Seq` Nop)) True
    checkFinIt (Fin (Loop (AwaitInt "a")))                        False
    checkFinIt (Fin (Loop (AwaitExt "A")))                        False
    checkFinIt (Fin (Nop `And` Nop `And` (EmitInt "a")))          True

  --------------------------------------------------------------------------
  describe "checkProg -- program is valid" $ do

    -- atomic statements --
    checkProgIt (Write "c" (Const 0)) True
    checkProgIt (AwaitExt "A")        True
    checkProgIt (AwaitInt "a")        True
    checkProgIt (EmitInt "a")         True
    checkProgIt (Break)               True
    checkProgIt (Nop)                 True
    checkProgIt (Error "")            True

    -- compound statements --
    checkProgIt (Var "x" Nop)          True
    checkProgIt (If (Const 0) Nop Break) True
    checkProgIt (Seq Break Nop)          True
    checkProgIt (Loop Break)             True
    checkProgIt (Loop Nop)               False
    checkProgIt (Every "A" Nop)          True
    checkProgIt (Every "A" (Fin Nop))    False
    checkProgIt (And Break Nop)          True
    checkProgIt (Or Nop (EmitInt "a"))   True
    checkProgIt (Pause "a" Nop)          True
    checkProgIt (Fin Nop)                True
    checkProgIt (Fin (Fin Nop))          False

    -- misc --
    checkProgIt (Nop `Seq` (Fin (Loop Break)))                        False
    checkProgIt (Nop `Seq` (Fin (Loop Nop)))                          False
    checkProgIt (Var "x" (Fin (Every "A" Nop)))                       False
    checkProgIt (Loop (Loop Break))                                   False
    checkProgIt (Loop (Loop (Seq Break Break)))                       False
    checkProgIt (AwaitInt "a" `Seq` (Fin Break) `Or` Nop)             False
    checkProgIt (AwaitInt "a" `Seq` (Every "A" (Fin Nop)) `Or` Nop)   False
    checkProgIt (Loop (Nop `Or` Loop (Loop (Loop (AwaitExt "A")))))   False
    checkProgIt (Loop (Break `Or` Loop (Loop (Loop (AwaitExt "A"))))) True

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b  = checkIt checkLoop p b
        checkFinIt p b   = checkIt checkFin p b
        checkEveryIt p b = checkIt checkEvery p b
        checkProgIt p b  = checkIt checkProg p b
