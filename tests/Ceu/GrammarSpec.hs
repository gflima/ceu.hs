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
    checkLoopIt (Loop (AwaitExt 0))                True
    checkLoopIt (Loop (AwaitInt 0))                False
    checkLoopIt (Loop (EmitInt 0))                 False
    checkLoopIt (Loop (Break))                     True
    checkLoopIt (Loop (Nop))                       False
    checkLoopIt (Loop (Error ""))                  False

    -- compound statements --
    checkLoopIt (Loop (Var "x" (Var "y" Break)))                 True
    checkLoopIt (Loop (Var "x" (Var "y" Nop)))                   False

    checkLoopIt (Loop (If (Const 0) Break Nop))                  False
    checkLoopIt (Loop (If (Const 0) (Fin Nop) Nop))              False
    checkLoopIt (Loop (If (Const 0) (Every 0 Nop) (AwaitExt 0))) True

    checkLoopIt (Loop (Nop `Seq` Nop `Seq` Break `Seq` Nop))     True
    checkLoopIt (Loop (Nop `Seq` Nop `Seq` (Loop Break)))        False
    checkLoopIt (Loop (Break `Seq` Loop Nop))                    True
    checkLoopIt (Loop (Nop `Seq` Loop Nop))                      False

    checkLoopIt (Loop (Loop (Loop (AwaitExt 0))))                True
    checkLoopIt (Loop (Loop Break))                              False
    checkLoopIt (Loop (Loop (Loop Break)))                       False
    checkLoopIt (Loop (Loop Break `Seq` Loop Break))             False
    checkLoopIt (Loop (Loop (AwaitExt 0) `Seq` Loop Nop))        True
    checkLoopIt (Loop (Loop (Seq Break Break)))                  False

    checkLoopIt (Loop (Nop `And` Nop `And` Nop))                 False
    checkLoopIt (Loop (Nop `Or` Nop `Or` Nop))                   False
    checkLoopIt (Loop (Every 0 Nop `Or` AwaitExt 0 `Or` Break))  True

    -- Fin always run in zero time.
    checkLoopIt (Loop (Fin Nop))                                 False
    checkLoopIt (Loop (Fin Break))                               False
    checkLoopIt (Loop (Fin (AwaitExt 0)))                        False
    checkLoopIt (Loop (Fin (Every 0 Nop)))                       False

  --------------------------------------------------------------------------
  describe "checkFin/Every -- no Loop/Break/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin (Write "x" (Const 0))) True
    checkFinIt (Fin (AwaitExt 0))          False
    checkFinIt (Fin (AwaitInt 0))          False
    checkFinIt (Fin (EmitInt 0))           True
    checkFinIt (Fin (Break))               False
    checkFinIt (Fin (Nop))                 True
    checkFinIt (Fin (Error ""))            True

    -- compound statements --
    checkFinIt (Fin (Var "x" Nop))                                True
    checkFinIt (Fin (Var "x" (Every 0 Nop)))                      False
    checkFinIt (Fin (If (Const 0) (Loop Break) (Nop)))            False
    checkFinIt (Fin (If (Const 0) (Write "x" (Const 0)) (Nop)))   True
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (AwaitExt 0) `Seq` Nop)) False
    checkFinIt (Fin (Nop `Seq` Nop `Seq` (EmitInt 0) `Seq` Nop))  True
    checkFinIt (Fin (Loop (AwaitInt 0)))                          False
    checkFinIt (Fin (Loop (AwaitExt 0)))                          False
    checkFinIt (Fin (Nop `And` Nop `And` (EmitInt 0)))            True

  --------------------------------------------------------------------------
  describe "checkProg -- program is valid" $ do

    -- atomic statements --
    checkProgIt (Write "c" (Const 0)) True
    checkProgIt (AwaitExt 0)          True
    checkProgIt (AwaitInt 0)          True
    checkProgIt (EmitInt 0)           True
    checkProgIt (Break)               True
    checkProgIt (Nop)                 True
    checkProgIt (Error "")            True

    -- compound statements --
    checkProgIt (Var "x" Nop)          True
    checkProgIt (If (Const 0) Nop Break) True
    checkProgIt (Seq Break Nop)          True
    checkProgIt (Loop Break)             True
    checkProgIt (Loop Nop)               False
    checkProgIt (Every 0 Nop)            True
    checkProgIt (Every 0 (Fin Nop))      False
    checkProgIt (And Break Nop)          True
    checkProgIt (Or Nop (EmitInt 0))     True
    checkProgIt (Fin Nop)                True
    checkProgIt (Fin (Fin Nop))          False

    -- misc --
    checkProgIt (Nop `Seq` (Fin (Loop Break)))                      False
    checkProgIt (Nop `Seq` (Fin (Loop Nop)))                        False
    checkProgIt (Var "x" (Fin (Every 0 Nop)))                       False
    checkProgIt (Loop (Loop Break))                                 False
    checkProgIt (Loop (Loop (Seq Break Break)))                     False
    checkProgIt (AwaitInt 0 `Seq` (Fin Break) `Or` Nop)             False
    checkProgIt (AwaitInt 0 `Seq` (Every 0 (Fin Nop)) `Or` Nop)     False
    checkProgIt (Loop (Nop `Or` Loop (Loop (Loop (AwaitExt 0)))))   False
    checkProgIt (Loop (Break `Or` Loop (Loop (Loop (AwaitExt 0))))) True

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ showProg p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b  = checkIt checkLoop p b
        checkFinIt p b   = checkIt checkFin p b
        checkEveryIt p b = checkIt checkEvery p b
        checkProgIt p b  = checkIt checkProg p b
