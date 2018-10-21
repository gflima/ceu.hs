module Ceu.EvalSpec (main, spec) where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Stmt as a datatype that can be fully evaluated.
instance NFData Stmt where
  rnf Nop = ()
  rnf (AwaitInt e) = ()
  rnf (Seq _ p q) = rnf p `seq` rnf q
  rnf (Loop' _ p q) = rnf p
  rnf (And' _ p q) = rnf p `seq` rnf q
  rnf (Or' _ p q) = rnf p `seq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "Env/Envs" $ do

    describe "envsGet envs id" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsGet [] "x")
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsGet [newEnv] "x")
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "pass: find in simple env" $
        envsGet [((["x"],[]),[("x",0)])] "x" -- CHECK THIS! --
        `shouldBe` ([],((["x"],[]),[("x",0)]),[])

      it "pass: find in complex env" $
        let envs = [((["z"],[]),[]),
                    ((["y"],[]),[("y",1)]),
                    ((["y"],[]),[("y",0)]),
                    ((["x"],[]),[])] in
          envsGet envs "y"
          `shouldBe` ([((["z"],[]),[])],
                      ((["y"],[]),[("y",1)]),
                      [((["y"],[]),[("y",0)]),((["x"],[]),[])])

    describe "envsWrite envs id val" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsWrite [] "x" 0)
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsWrite [newEnv] "x" 0)
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "pass: 1st write" $
        envsWrite [((["x"],[]),[])] "x" 0 `shouldBe` [((["x"],[]),[("x",0)])]

      it "pass: 2st write" $
        envsWrite [((["x"],[]),[("x",0)])] "x" 1
        `shouldBe` [((["x"],[]),[("x",1),("x",0)])]

      it "pass: 1st write in inner env" $
        envsWrite [newEnv,((["x"],[]),[]),((["x"],[]),[("x",0)])] "x" 1
        `shouldBe` [newEnv,((["x"],[]),[("x",1)]),((["x"],[]),[("x",0)])]

      it "pass: 2nd write in inner env" $
        envsWrite [newEnv,((["x"],[]),[("x",1)]),((["x"],[]),[("x",0)])] "x" 2
        `shouldBe` [newEnv,((["x"],[]),[("x",2),("x",1)]),((["x"],[]),[("x",0)])]

    describe "envsRead envs id" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsRead [] "x")
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsRead [newEnv] "x")
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (envsRead [((["x"],[]),[])] "x")
        `shouldThrow` errorCall "envsRead: uninitialized variable: x"

      it "pass: read in simple env" $
        envsRead [((["x"],[]),[("x",0)])] "x" `shouldBe` 0

      it "pass: read in complex env" $
        let envs = [newEnv,
                    ((["y"],[]),[]),
                    ((["y","x"],[]),[("y",1),("y",0),("x",1),("x",0)]),
                    ((["x"],[]),[("x",99)])] in
          envsRead envs "x" `shouldBe` 1

    describe "envsEval envs exp" $ do
      it "pass: envs == [] && exp == (Const _)" $
        envsEval [] (Const 0) `shouldBe` 0 -- CHECK THIS! --

      it "fail: envs == [] && exp != (Const _) (bad environment)" $
        forceEval (envsEval [] (Read "x"))
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsEval [newEnv] (Read "x"))
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (envsEval [((["x"],[]),[])] (Read "x"))
        `shouldThrow` errorCall "envsRead: uninitialized variable: x"

      it "pass: eval in simple env" $
        let envs = [((["x","y"],[]),[("x",1),("y",2)])] in
          envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let envs = [((["y"],[]),[("y",2)]),
                    ((["y","x"],[]),[("y",0),("x",1)]),
                     ((["x"],[]),[("x",0)])] in
          envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "nst1" $ do

    -- error --
    describe "(Error \"erro\")" $ do
      it "fail: error \"erro\"" $
        (forceEval $ nst1 (Error "erro", 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "Runtime error: erro"

    -- block --
    describe "(Block [vars] p)" $ do
      it "pass: Block [] Nop" $
        nst1 (Block 0 ([],[]) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 Nop (Restore 1), 0, Nothing, [newEnv,newEnv])

      it "pass: Block [\"x\"] p" $
        nst1 (Block 0 (["x"],[]) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 Nop (Restore 1), 0, Nothing, [((["x"],[]),[]),newEnv])

      it "pass: Block [\"x\",\"y\"] p" $
        nst1 (Block 0 (["x","y"],[]) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 Nop (Restore 1), 0, Nothing, [((["x","y"],[]),[]),newEnv])

    -- restore --
    describe "(Restore envs)" $ do
      it "pass: [e1,e2] " $
        nst1 (Restore 1, 0, Nothing, [newEnv,newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        forceEval (nst1 (Write "x" (Read "y"), 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        forceEval (nst1 (Write "x" (Const 1), 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "pass: [x=?] x=1" $
        nst1 (Write "x" (Const 1), 0, Nothing, [((["x"],[]),[])])
        `shouldBe` (Nop, 0, Nothing, [((["x"],[]),[("x",1)])])

      it "pass: [x=1] x=2" $
        nst1 (Write "x" (Const 2), 0, Nothing, [((["x"],[]),[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [((["x"],[]),[("x",2),("x",1)])])

      it "fail: [x=?,y=?] x=y (uninitialized variable)" $
        forceEval (nst1 (Write "x" (Read "y"), 0, Nothing,
                          [((["x","y"],[]),[("x",1)])]))
        `shouldThrow` errorCall "envsRead: uninitialized variable: y"

      it "pass: nop; x=1" $
        nst1 (Seq 0 Nop (Write "x" (Const 1)), 0, Nothing, [newEnv])
        `shouldBe` ((Write "x" (Const 1)), 0, Nothing, [newEnv])

      it "fail: [x=1] y=x+2 (undeclared variable)" $
        forceEval (nst1 (Write "y" (Read "x" `Add` Const 2), 0, Nothing,
                          [((["x"],[]),[("x",1)])]))
        `shouldThrow` errorCall "envsGet: undeclared variable: y"

      it "pass: [x=1,y=?] y=x+2" $
        nst1 (Write "y" (Read "x" `Add` Const 2), 0, Nothing,
               [((["x","y"],[]),[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [((["x","y"],[]),[("y",3),("x",1)])])

      it "transit: [x=?] x=-(5+1)" $
        nst1 (Write "x" (Umn (Const 5 `Add` Const 1)), 0, Nothing,
               [((["x"],[]),[])])
        `shouldBe` (Nop, 0, Nothing, [((["x"],[]), [("x",-6)])])

    -- emit-int --
    describe "(EmitInt e')" $ do
      it "pass: lvl == 0" $
        nst1 (EmitInt "e", 0, Nothing, [newEnv])
        `shouldBe` (CanRun 0, 0, Just "e", [newEnv])

      it "pass: lvl > 0" $
        nst1 (EmitInt "f", 3, Nothing, [newEnv])
        `shouldBe` (CanRun 3, 3, Just "f", [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (EmitInt "f", 3, Just "f", [(([],[]),[])]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- can-run --
    describe "(CanRun n)" $ do
      it "pass: n == lvl" $
        nst1 (CanRun 0, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: n == lvl" $
        nst1 (CanRun 8, 8, Nothing, [newEnv])
        `shouldBe` (Nop, 8, Nothing, [newEnv])

      it "fail: n > lvl (cannot advance)" $
        forceEval (nst1 (CanRun 8, 6, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: n < lvl (cannot advance)" $
        forceEval (nst1 (CanRun 8, 12, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (CanRun 0, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-nop --
    describe "(Seq Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq 0 Nop Break, 3, Nothing, [newEnv])
        `shouldBe` (Break, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-brk --
    describe "(Seq Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq 0 Break Nop, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq 0 Break (EmitInt "z"), 3, Nothing, [newEnv])
        `shouldBe` (Break, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq 0 Break Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-adv --
    describe "(Seq p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq 1 (Seq 0 Nop Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 1 Nop Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq 1 (Seq 0 (EmitInt "z") Nop) Nop, 3, Nothing, [newEnv])
        `shouldBe` (Seq 1 (Seq 0 (CanRun 3) Nop) Nop, 3, Just "z", [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq 1 (Seq 0 Nop Nop) Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Seq 1 (Fin 0 Nop) Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- if-true/false --
    describe "(If exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (nst1 (If 0 (Read "x") Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable: x"

      it "pass: x == 0" $
        nst1 (If 0 (Read "x") Nop Break, 0, Nothing, [((["x"],[]),[("x",0)])])
        `shouldBe` (Break, 0, Nothing, [((["x"],[]),[("x",0)])])

      it "pass: x /= 0" $
        nst1 (If 0 (Read "x") Nop Break, 0, Nothing, [((["x"],[]),[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [((["x"],[]),[("x",1)])])

    -- loop-expd --
    describe "(Loop p)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop 0 Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 (Loop' 0 Nop Nop) (Restore 1), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop 1 (Seq 0 Nop (EmitInt "z")), 3, Nothing, [newEnv])
        `shouldBe`
        (Seq 1 (Loop' 1 (Seq 0 Nop (EmitInt "z")) (Seq 0 Nop (EmitInt "z")))
             (Restore 1),
          3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop 0 Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        nst1 (Loop 1 (Fin 0 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq 1 (Loop' 1 (Fin 0 Nop) (Fin 0 Nop)) (Restore 1),
                     0, Nothing, [newEnv])

    -- loop-nop --
    describe "(Loop' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Loop 0 Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' 0 Nop (EmitInt "z"), 3, Nothing, [newEnv])
        `shouldBe` (Loop 0 (EmitInt "z"), 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' 0 Nop (Fin 1 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Loop 0 (Fin 1 Nop), 0, Nothing, [newEnv])

    -- loop-brk --
    describe "(Loop' Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' 0 Break Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' 0 Break (Seq 1 (EmitInt "z") Nop), 3, Nothing, [newEnv])
        `shouldBe` (Nop, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' 0 Break Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' 0 Break (Fin 1 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

    -- loop-adv --
    describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' 0 (Seq 1 Nop Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Loop' 0 Nop Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' 0 (Seq 1 (EmitInt "z") Nop) Break, 3, Nothing, [newEnv])
        `shouldBe` (Loop' 0 (Seq 1 (CanRun 3) Nop) Break, 3, Just "z", [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' 0 (Seq 1 Nop Nop) Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Loop' 0 (Fin 1 Nop) Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Loop' 0 (Seq 1 Nop Nop) (Fin 2 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Loop' 0 Nop (Fin 2 Nop), 0, Nothing, [newEnv])

    -- and-expd --
    describe "(And p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (And' 0 Nop (Seq 0 (CanRun 0) Nop), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And 1 (Seq 1 Nop (EmitInt "z")) (Seq 2 Nop Nop),
               3, Nothing, [newEnv])
        `shouldBe` (And' 1 (Seq 1 Nop (EmitInt "z"))
                           (Seq 1 (CanRun 3) (Seq 2 Nop Nop)), 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And 1 (Fin 0 Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (And' 1 (Fin 0 Nop) (Seq 1 (CanRun 0) Nop),
                     0, Nothing, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And 0 Nop (Fin 1 Nop), 0, Nothing, [newEnv])
        `shouldBe` (And' 0 Nop (Seq 0 (CanRun 0) (Fin 1 Nop)),
                     0, Nothing, [newEnv])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (And 1 (Fin 0 Nop) (Fin 2 Nop), 0, Nothing, [newEnv])
        `shouldBe` (And' 1 (Fin 0 Nop) (Seq 1 (CanRun 0) (Fin 2 Nop)),
                     0, Nothing, [newEnv])

    -- and-nop1 --
    describe "(And' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And' 0 Nop (EmitInt "z"), 3, Nothing, [newEnv])
        `shouldBe` (EmitInt "z", 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (And' 0 Nop (Fin 1 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Fin 1 Nop, 0, Nothing, [newEnv])

      it "pass: q == Nop" $
        nst1 (And' 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: q == Break" $
        nst1 (And' 0 Nop Break, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

    -- and-brk1 --
    describe "(And' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitExt "A") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' 0 Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0" $
        let q = (AwaitInt "e") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' 0 Break q, 3, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear q) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' 0 Break (Block 1 ([],[]) Nop), 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin 0 (Seq 1 Nop Nop) in
          (clear q `shouldBe` (Seq 1 Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (And' 0 Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' 0 (Seq 0 (AwaitExt "A") (Fin 0 Nop))
                    (And' 1 (Fin 0 (EmitInt "f"))
                          (Or' 3 (Fin 2 (Seq 2 (EmitInt "g") (EmitInt "h")))
                            (Seq 2 (AwaitInt "e") (Fin 2 (EmitInt "i")))))
            clear_q = (Seq 0 Nop (Seq 1 (EmitInt "f")
                             (Seq 3 (Seq 2 (EmitInt "g") (EmitInt "h")) Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' 0 Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear q) Break, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (And' 0 Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (And' 0 Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-nop2 --
    describe "(And' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        nst1 (And' 1 (Fin 0 Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Fin 0 Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0 && isBlocked p" $
        nst1 (And' 2 (Seq 0 (Fin 1 Nop) Nop) Nop, 3, Nothing, [newEnv])
        `shouldBe` (Seq 0 (Fin 1 Nop) Nop, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' 1 (Fin 0 Nop) Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: p == Nop" $
        nst1 (And' 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' 0 Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-brk2 --
    describe "(And' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "f") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (And' 0 p Break, 0, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin 0 (Seq 1 Nop Nop) in
          (clear p `shouldBe` (Seq 1 Nop Nop))
          >>
          (nst1 (And' 0 p Break, 3, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear p) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' 1 (Fin 0 Nop) Break, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' 2 (Seq 0 (AwaitExt "A") (Fin 1 Nop))
                      (And' 4 (Fin 3 (EmitInt "f"))
                            (Or' 5 (Fin 6 (Seq 7 (EmitInt "g") (EmitInt "h")))
                            (Seq 8 (AwaitInt "e") (Fin 9 (EmitInt "i")))))
            clear_p = (Seq 2 Nop (Seq 4 (EmitInt "f")
                      (Seq 5 (Seq 7 (EmitInt "g") (EmitInt "h")) Nop))) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' 0 p Break, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: p == Nop" $
        nst1 (And' 0 Nop Break, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' 0 Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-adv --
    describe "(And' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' 1 (Seq 0 Nop Nop) (Seq 2 Break Break), 0, Nothing, [newEnv])
        `shouldBe` (And' 1 Nop (Seq 2 Break Break), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And' 1 (Seq 0 (EmitInt "z") Nop) (Seq 2 (EmitInt "y") Nop),
               3, Nothing, [newEnv])
        `shouldBe` (And' 1 (Seq 0 (CanRun 3) Nop) (Seq 2 (EmitInt "y") Nop),
                     3, Just "z", [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' 1 (Seq 0 Nop Nop) (Seq 2 Nop Nop),
                         0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And' 1 (Fin 0 Nop) (Seq 2 (EmitInt "z") Nop),
               3, Nothing, [newEnv])
        `shouldBe` (And' 1 (Fin 0 Nop) (Seq 2 (CanRun 3) Nop),
                     3, Just "z", [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And' 0 (EmitInt "z") (AwaitInt "z"), 3, Nothing, [newEnv])
        `shouldBe` (And' 0 (CanRun 3) (AwaitInt "z"), 3, Just "z", [newEnv])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (And' 0 (AwaitInt "h") (AwaitInt "i"),
                          0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- or-expd --
    describe "(Or p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or 0 Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 (Or' 0 Nop (Seq 0 (CanRun 0) Nop)) (Restore 1),
                     0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Or 1 (Seq 0 Nop (EmitInt "z")) (Seq 2 Nop Nop), 3, Nothing, [newEnv])
        `shouldBe` (Seq 1 (Or' 1 (Seq 0 Nop (EmitInt "z"))
                          (Seq 1 (CanRun 3) (Seq 2 Nop Nop))) (Restore 1),
                     3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or 0 (Fin 1 Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq 0 (Or' 0 (Fin 1 Nop) (Seq 0 (CanRun 0) Nop)) (Restore 1),
                     0, Nothing, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or 1 Nop (Fin 0 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq 1 (Or' 1 Nop (Seq 1 (CanRun 0) (Fin 0 Nop))) (Restore 1),
                     0, Nothing, [newEnv])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (Or 1 (Fin 0 Nop) (Fin 2 Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq 1 (Or' 1 (Fin 0 Nop) (Seq 1 (CanRun 0) (Fin 2 Nop)))
                     (Restore 1), 0, Nothing, [newEnv])

    -- or-nop1 --
    describe "(Or' Nop q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "e") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' 0 Nop q, 0, Nothing, [newEnv])
           `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "pass: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' 0 Nop q, 3, Nothing, [newEnv])
           `shouldBe` (clear q, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' 0 Nop Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = (Fin 0 Nop) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' 0 Nop q, 0, Nothing, [newEnv])
           `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' 2 (Seq 0 (AwaitExt "A") (Fin 1 Nop))
                    (And' 4 (Fin 3 (EmitInt "f"))
                          (Or' 7 (Fin 5 (Seq 6 (EmitInt "g") (EmitInt "h")))
                            (Seq 9 (AwaitInt "e") (Fin 9 (EmitInt "i")))))
            clear_q = (Seq 2 Nop (Seq 4 (EmitInt "f")
                      (Seq 7 (Seq 6 (EmitInt "g") (EmitInt "h")) Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' 0 Nop q, 0, Nothing, [newEnv])
            `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' 0 Nop Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' 0 Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-brk1 --
    describe "(Or' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "e") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' 0 Break q, 0, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear q) Break, 0, Nothing, [newEnv]))

      it "transit: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q`shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' 0 Break q, 3, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear q) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' 0 Break Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin 0 (Seq 1 Nop Nop) in
          (clear q `shouldBe` (Seq 1 Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (Or' 0 Break q, 0, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' 2 (Seq 0 (AwaitExt "A") (Fin 1 Nop))
                    (And' 4 (Fin 3 (EmitInt "f"))
                          (Or' 7 (Fin 5 (Seq 7 (EmitInt "g") (EmitInt "h")))
                            (Seq 8 (AwaitInt "e") (Fin 9 (EmitInt "i")))))
            clear_q = (Seq 2 Nop (Seq 4 (EmitInt "f")
                      (Seq 7 (Seq 7 (EmitInt "g") (EmitInt "h")) Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' 0 Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 clear_q Break, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' 0 Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' 0 Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-nop2 --
    describe "(Or' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin 0 Nop) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' 0 p Nop, 0, Nothing, [newEnv])
            `shouldBe` (clear p, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq 0 (Fin 1 Nop) Nop in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' 0 p Nop, 3, Nothing, [newEnv])
            `shouldBe` (clear p, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' 0 (Fin 1 Nop) Nop, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' 0 Nop Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' 0 Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-brk2 --
    describe "(Or' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "f") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' 0 p Break, 0, Nothing, [newEnv])
           `shouldBe` (Seq 0 (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin 0 (Seq 0 Nop Nop) in
          (clear p `shouldBe` Seq 0 Nop Nop)
          >>                    -- clear p == Nop; Nop
          (nst1 (Or' 0 p Break, 3, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear p) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' 1 (Fin 0 Nop) Break, 0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' 2 (Seq 0 (AwaitExt "A") (Fin 1 Nop))
                    (And' 4 (Fin 3 (EmitInt "f"))
                          (Or' 7 (Fin 6 (Seq 5 (EmitInt "g") (EmitInt "h")))
                            (Seq 8 (AwaitInt "e") (Fin 9 (EmitInt "i")))))
            clear_p = (Seq 2 Nop (Seq 4 (EmitInt "f") (Seq 7
                      (Seq 5 (EmitInt "g") (EmitInt "h")) Nop))) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' 0 p Break, 0, Nothing, [newEnv])
            `shouldBe` (Seq 0 (clear p) Break, 0, Nothing, [newEnv]))

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' 0 Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' 0 Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-adv --
    describe "(Or' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or' 1 (Seq 0 Nop Nop) (Seq 2 Break Break), 0, Nothing, [newEnv])
        `shouldBe` (Or' 1 Nop (Seq 2 Break Break), 0, Nothing, [newEnv])

      it "psas: lvl > 0" $
        nst1 (Or' 1 (Seq 0 (EmitInt "z") Nop) (Seq 2 (EmitInt "y") Nop),
               3, Nothing, [newEnv])
        `shouldBe` (Or' 1 (Seq 0 (CanRun 3) Nop) (Seq 2 (EmitInt "y") Nop),
                     3, Just "z", [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' 1 (Seq 0 Nop Nop) (Seq 2 Nop Nop),
                          0, Just "f", [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or' 1 (Fin 0 Nop) (Seq 2 (EmitInt "z") Nop), 3, Nothing, [newEnv])
        `shouldBe` (Or' 1 (Fin 0 Nop) (Seq 2 (CanRun 3) Nop), 3, Just "z", [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or' 0 (EmitInt "z") (AwaitInt "z"), 3, Nothing, [newEnv])
        `shouldBe` (Or' 0 (CanRun 3) (AwaitInt "z"), 3, Just "z", [newEnv])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (Or' 0 (AwaitInt "h") (AwaitInt "i"),
                          0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

  --------------------------------------------------------------------------
  describe "nsts" $ do
    describe "zero steps (program is blocked)" $ do

      nstsItPass
        (AwaitExt "A", 0, Nothing, [newEnv])
        (AwaitExt "A", 0, Nothing, [newEnv])

      nstsItPass
        (AwaitInt "e", 0, Nothing, [newEnv])
        (AwaitInt "e", 0, Nothing, [newEnv])

      nstsItPass
        (Seq 0 (AwaitInt "e") Nop, 0, Nothing, [newEnv])
        (Seq 0 (AwaitInt "e") Nop, 0, Nothing, [newEnv])

      nstsItPass
        (Every 0 "e" Nop, 0, Nothing, [newEnv])
        (Every 0 "e" Nop, 0, Nothing, [newEnv])

      nstsItPass
        (Fin 1 (Seq 0 Nop Nop), 0, Nothing, [newEnv])
        (Fin 1 (Seq 0 Nop Nop), 0, Nothing, [newEnv])

      nstsItPass
        (And' 0 (AwaitExt "A") (Fin 1 Nop), 0, Nothing, [newEnv])
        (And' 0 (AwaitExt "A") (Fin 1 Nop), 0, Nothing, [newEnv])

      nstsItPass
        (Or' 0 (AwaitExt "A") (Fin 1 Nop), 0, Nothing, [newEnv])
        (Or' 0 (AwaitExt "A") (Fin 1 Nop), 0, Nothing, [newEnv])

      nstsItFail "nst1: cannot advance"
        (CanRun 5, 0, Nothing, [newEnv])

    describe "zero steps (no nst1-rule applies)" $ do

      nstsItPass
        (Nop, 0, Nothing, [newEnv])
        (Nop, 0, Nothing, [newEnv])

      nstsItPass
        (Break, 0, Nothing, [newEnv])
        (Break, 0, Nothing, [newEnv])

    describe "one+ steps" $ do

      nstsItPass
        (Block 0 (["x"],[]) (Write "x" (Const 0)), 3, Nothing, [newEnv])
        (Nop, 3, Nothing, [newEnv])

      nstsItPass
        (EmitInt "z", 3, Nothing, [newEnv])
        (CanRun 3, 3, Just "z", [newEnv])

      nstsItPass
        (CanRun 3, 3, Nothing, [newEnv])
        (Nop, 3, Nothing, [newEnv])

      nstsItPass
        ((Seq 0 Nop (Seq 1 Nop (Seq 2 Nop (Seq 3 Break Nop)))), 0, Nothing, [newEnv])
        (Break, 0, Nothing, [newEnv])

      nstsItPass
        (Seq 1 (Loop 0 Break) (Seq 2 Nop (Seq 3 Nop (Seq 4 (EmitInt "z") Break))),
          3, Nothing, [newEnv])
        (Seq 4 (CanRun 3) Break, 3, Just "z", [newEnv])

      nstsItPass
        ((And 2 (Seq 0 (Loop 1 Break) Nop) (Seq 3 (EmitInt "z") Nop)), 3, Nothing, [newEnv])
        (Seq 3 (CanRun 3) Nop, 3, Just "z", [newEnv])

      nstsItPass
        (Or 2 (Seq 0 (Loop 1 Break) Nop) (Seq 3 (EmitInt "z") Nop), 3, Nothing, [newEnv])
        (Nop, 3, Nothing, [newEnv])

      nstsItPass
        ((Loop 2
          (And 0 (Seq 1 Nop (AwaitInt "h"))
           (Or 3 (AwaitExt "Z") (Seq 4 Nop Break)))), 0, Nothing, [newEnv])
        (Nop, 0, Nothing, [newEnv])
  --------------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 (Nop, 0, Just "f", [newEnv])
        `shouldBe` (Nop, 1, Nothing, [newEnv])

      it "pass: lvl > 0" $
        out1 (Seq 0 (AwaitInt "f") Break, 3, Just "f", [newEnv])
        `shouldBe` (Seq 0 Nop Break, 4, Nothing, [newEnv])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq 0 (AwaitInt "g") Break, 3, Just "f", [newEnv])
        `shouldBe` (Seq 0 (AwaitInt "g") Break, 4, Nothing, [newEnv])

    -- pop --
    describe "pop" $ do
      it "fail: lvl == 0 (cannot advance)" $
        forceEval (out1 (Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "pass: lvl > 0 && isNstIrreducible p" $
        out1 (Nop, 33, Nothing, [newEnv])
        `shouldBe` (Nop, 32, Nothing, [newEnv])

      it "pass: lvl > 0 && not (nstIrreducible p)" $
        forceEval (out1 (Seq 0 Nop Nop, 1, Nothing, [newEnv]))
        `shouldThrow` errorCall "outPop: cannot advance"

  --------------------------------------------------------------------------
  describe "nsts_out1_s" $ do
    describe "zero steps (no out-rule applies)" $ do
      it "pass: lvl == 0 && isNstIrreducible p" $
        let d = (Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` True)
          >> (isIrreducible d `shouldBe` True)

      it "pass: lvl == 0 && not (isNstIrreducible p)" $
        let d = (Seq 0 Nop Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` False)
          >> (isIrreducible d `shouldBe` False)

    describe "one+ pops" $ do
      it "pass: lvl > 0" $
        let d = (Nop, 13, Nothing, [newEnv])
            d' = (Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

    describe "one push followed by one+ pops" $ do
      it "pass: lvl == 0 (do nothing)" $ -- CHECK THIS! --
        let d = (AwaitInt "h", 0, Just "h", [newEnv])
            d' = (AwaitInt "h", 0, Just "h", [newEnv]) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          -- >> (isIrreducible d' `shouldBe` True)

      it "pass: lvl > 0" $
        let d = (AwaitInt "h", 88, Just "h", [newEnv])
            d' = (Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      (And 1 (Seq 0 Nop (AwaitInt "h")) (Seq 2 Nop (Fin 3 Nop)), "h", [(([],[]),[])])
      (And' 1 (AwaitInt "h") (Fin 3 Nop), [(([],[]),[])])

    reactionItPass
      (And 1 (Seq 0 Nop (AwaitInt "h")) (Seq 2 Nop (EmitInt "h")), "f", [(([],[]),[])])
      (Nop, [(([],[]),[])])

  --------------------------------------------------------------------------
  describe "evalProg" $ do

    evalProgItPass 11
      [] (G.Block (["a"],[])
           (G.Write "a" (Const 1) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItFail "envsRead: uninitialized variable: ret"
      [] (G.Block (["a"],[])
           (G.Block (["ret"],[])
             (G.Write "a" (Const 1) `G.Seq`
              G.Write "ret" (Read "a" `Add` Const 10))))

    evalProgItPass 1
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Block (["ret"],[]) (G.Write "ret" (Const 99)))

    evalProgItPass 11
      [] (G.Block (["a"],[])
           (G.Write "a" (Const 1) `G.Seq`
            G.Block (["a"],[]) (G.Write "a" (Const 99)) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 2
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Block ([],[]) (G.Write "ret" (Const 2)))

    evalProgItPass 11
      [] (G.Block (["a"],[])
           (G.Write "a" (Const 1) `G.Seq`
            G.Or
             (G.Block (["a"],[]) (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
             (G.Nop) `G.Seq`
           G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (G.Or
           (G.Block ([],[]) (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
           (G.Nop))

    evalProgItPass 11
      [] (G.Block (["a"],[])
           (G.Write "a" (Const 1) `G.Seq`
            G.Loop (G.And
                  (G.Block (["a"],[]) (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
                  (G.Break)) `G.Seq`
             G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (G.Loop (G.And
                 (G.Block ([],[]) (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
                 (G.Break)))

    evalProgItPass 5 [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.And
        ((G.AwaitInt "e") `G.Seq` (G.Write "ret" (Const 5)))
        (G.EmitInt "e")
      ))

    evalProgItPass 5 [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.Or
        ((G.AwaitInt "e") `G.Seq` (G.Write "ret" (Const 5)))
        (G.Or (G.Fin (G.EmitInt "e")) G.Nop)
      ))

    -- multiple inputs

    evalProgItPass 1
      ["A"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      [] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      ["B"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: pending inputs"
      ["A","A"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItPass 1
      ["A","B"] (G.AwaitExt "A" `G.Seq` G.AwaitExt "B" `G.Seq` G.Write "ret" (Const 1))

    evalProgItPass 1 [] (G.Write "ret" (Const 1))

      where
        nstsItPass (p,n,e,envs) (p',n',e',envs') =
          (it (printf "pass: %s -> %s#" (showProg p) (showProg p'))
           ((nsts (p,n,e,envs) `shouldBe` (p',n',e',envs'))
             >> (isNstIrreducible (p',n',e',envs') `shouldBe` True)))

        nstsItFail err (p,n,e,envs) =
          (it (printf "fail: %s ***%s" (showProg p) err)
           (forceEval (nsts (p,n,e,envs)) `shouldThrow` errorCall err))

        reactionItPass (p,e,envs) (p',envs') =
          (it (printf "pass: %s | %s -> %s" e (showProg p) (showProg p'))
            (reaction (p,e,envs) `shouldBe` (p',envs')))

        evalProgItPass res hist prog =
          (it (printf "pass: %s | %s ~>%d" (show hist) (G.showProg prog) res) $
            (evalProg prog hist `shouldBe` res))

        evalProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg prog) err) $
            (forceEval (evalProg prog hist) `shouldThrow` errorCall err))
