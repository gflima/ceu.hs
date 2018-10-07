module CeuSpec where

import Ceu
import Control.DeepSeq
import Control.Exception
import Test.Hspec

-- Declare Stmt as a datatype that can be fully evaluated.
instance NFData Stmt where
  rnf Nop = ()
  rnf (AwaitInt e) = ()
  rnf (Seq p q) = rnf p `seq` rnf q
  rnf (Loop' p q) = rnf p
  rnf (And' p q) = rnf p `seq` rnf q
  rnf (Or' p q) = rnf p `seq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec $ do

  -- Env/Envs --------------------------------------------------------------
  describe "Env/Envs" $ do
    describe "envsDcl envs id" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsDcl [] "x")
        `shouldThrow` errorCall "envsDcl: bad environment"

      it "pass: 1st declaration" $
        envsDcl [newEnv] "x" `shouldBe` [(["x"],[])]

      it "pass: 2nd declaration" $
        envsDcl [(["x"],[])] "y" `shouldBe` [(["y","x"],[])]

      it "pass: redeclaration" $  -- CHECK THIS! --
        envsDcl [(["y","x"],[])] "x" `shouldBe` [(["x","y","x"],[])]

      it "pass: redeclaration in inner env" $
        envsDcl (newEnv:[(["x"],[("x",0)])]) "x"
        `shouldBe` [(["x"],[]),(["x"],[("x",0)])]

    describe "envsGet envs id" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsGet [] "x")
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsGet [newEnv] "x")
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "pass: find in simple env" $
        envsGet [(["x"],[("x",0)])] "x" -- CHECK THIS! --
        `shouldBe` ([],(["x"],[("x",0)]),[])

      it "pass: find in complex env" $
        let envs = [(["z"],[]),
                    (["y"],[("y",1)]),
                    (["y"],[("y",0)]),
                    (["x"],[])] in
          envsGet envs "y"
          `shouldBe` ([(["z"],[])],
                      (["y"],[("y",1)]),
                      [(["y"],[("y",0)]),(["x"],[])])

    describe "envsWrite envs id val" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsWrite [] "x" 0)
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsWrite [newEnv] "x" 0)
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "pass: 1st write" $
        envsWrite [(["x"],[])] "x" 0 `shouldBe` [(["x"],[("x",0)])]

      it "pass: 2st write" $
        envsWrite [(["x"],[("x",0)])] "x" 1
        `shouldBe` [(["x"],[("x",1),("x",0)])]

      it "pass: 1st write in inner env" $
        envsWrite [newEnv,(["x"],[]),(["x"],[("x",0)])] "x" 1
        `shouldBe` [newEnv,(["x"],[("x",1)]),(["x"],[("x",0)])]

      it "pass: 2nd write in inner env" $
        envsWrite [newEnv,(["x"],[("x",1)]),(["x"],[("x",0)])] "x" 2
        `shouldBe` [newEnv,(["x"],[("x",2),("x",1)]),(["x"],[("x",0)])]

    describe "envsRead envs id" $ do
      it "fail: envs == [] (bad environment)" $
        forceEval (envsRead [] "x")
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsRead [newEnv] "x")
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "fail: uninitialized variable" $
        forceEval (envsRead [(["x"],[])] "x")
        `shouldThrow` errorCall "envsRead: uninitialized variable"

      it "pass: read in simple env" $
        envsRead [(["x"],[("x",0)])] "x" `shouldBe` 0

      it "pass: read in complex env" $
        let envs = [newEnv,
                    (["y"],[]),
                    (["y","x"],[("y",1),("y",0),("x",1),("x",0)]),
                    (["x"],[("x",99)])] in
          envsRead envs "x" `shouldBe` 1

    describe "envsEval envs exp" $ do
      it "pass: envs == [] && exp == (Const _)" $
        envsEval [] (Const 0) `shouldBe` 0 -- CHECK THIS! --

      it "fail: envs == [] && exp != (Const _) (bad environment)" $
        forceEval (envsEval [] (Read "x"))
        `shouldThrow` errorCall "envsGet: bad environment"

      it "fail: undeclared variable" $
        forceEval (envsEval [newEnv] (Read "x"))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "fail: uninitialized variable" $
        forceEval (envsEval [(["x"],[])] (Read "x"))
        `shouldThrow` errorCall "envsRead: uninitialized variable"

      it "pass: eval in simple env" $
        let envs = [(["x","y"],[("x",1),("y",2)])] in
          envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let envs = [(["y"],[("y",2)]),
                    (["y","x"],[("y",0),("x",1)]),
                     (["x"],[("x",0)])] in
          envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

  -- nst1 ------------------------------------------------------------------
  describe "nst1" $ do

    -- block --
    describe "(Block p)" $ do
      it "pass: Block Nop" $
        nst1 (Block Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq Nop (Envs' 1), 0, Nothing, [newEnv,newEnv])

    -- envs' --
    describe "(Envs' envs)" $ do
      it "pass: [e1,e2] " $
        nst1 (Envs' 1, 0, Nothing, [newEnv,newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

    -- var --
    describe "(Var id)" $ do
      it "pass: x" $
        nst1 (Var "x", 0, Nothing, [([],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[])])

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        forceEval (nst1 (Write "x" (Read "y"), 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "fail: [] x=1 (undeclared variable)" $
        forceEval (nst1 (Write "x" (Const 1), 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "pass: [x=?] x=1" $
        nst1 (Write "x" (Const 1), 0, Nothing, [(["x"],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",1)])])

      it "pass: [x=1] x=2" $
        nst1 (Write "x" (Const 2), 0, Nothing, [(["x"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",2),("x",1)])])

      it "fail: [x=?,y=?] x=y (uninitialized variable)" $
        forceEval (nst1 (Write "x" (Read "y"), 0, Nothing,
                          [(["x","y"],[("x",1)])]))
        `shouldThrow` errorCall "envsRead: uninitialized variable"

      it "pass: nop; x=1" $
        nst1 (Seq Nop (Write "x" (Const 1)), 0, Nothing, [newEnv])
        `shouldBe` ((Write "x" (Const 1)), 0, Nothing, [newEnv])

      it "fail: [x=1] y=x+2 (undeclared variable)" $
        forceEval (nst1 (Write "y" (Read "x" `Add` Const 2), 0, Nothing,
                         [(["x"],[("x",1)])]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "pass: [x=1,y=?] y=x+2" $
        nst1 (Write "y" (Add (Read "x") (Const 2)), 0, Nothing,
               [(["x","y"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x","y"],[("y",3),("x",1)])])

      it "transit: [x=?] x=-(5+1)" $
        nst1 (Write "x" (Umn (Add (Const 5) (Const 1))), 0, Nothing,
               [(["x"],[])])
        `shouldBe` (Nop, 0, Nothing, [(["x"], [("x",-6)])])

    -- emit-int --
    describe "(EmitInt e')" $ do
      it "pass: lvl == 0" $
        nst1 (EmitInt 0, 0, Nothing, [newEnv])
        `shouldBe` (CanRun 0, 0, Just 0, [newEnv])

      it "pass: lvl > 0" $
        nst1 (EmitInt 1, 3, Nothing, [newEnv])
        `shouldBe` (CanRun 3, 3, Just 1, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (EmitInt 1, 3, Just 1, [([],[])]))
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
        forceEval (nst1 (CanRun 0, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-nop --
    describe "(Seq Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq Nop Break, 3, Nothing, [newEnv])
        `shouldBe` (Break, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-brk --
    describe "(Seq Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq Break Nop, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq Break (EmitInt 8), 3, Nothing, [newEnv])
        `shouldBe` (Break, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq Break Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- seq-adv --
    describe "(Seq p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq (Seq Nop Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq Nop Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Seq (Seq (EmitInt 8) Nop) Nop, 3, Nothing, [newEnv])
        `shouldBe` (Seq (Seq (CanRun 3) Nop) Nop, 3, Just 8, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq (Seq Nop Nop) Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Seq (Fin Nop) Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- if-true/false --
    describe "(If exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (nst1 (If (Read "x") Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "envsGet: undeclared variable"

      it "pass: x == 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",0)])])
        `shouldBe` (Break, 0, Nothing, [(["x"],[("x",0)])])

      it "pass: x /= 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",1)])])
        `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",1)])])

    -- loop-expd --
    describe "(Loop p)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq (Loop' Nop Nop) (Envs' 1), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop (Seq Nop (EmitInt 8)), 3, Nothing, [newEnv])
        `shouldBe`
        (Seq (Loop' (Seq Nop (EmitInt 8)) (Seq Nop (EmitInt 8))) (Envs' 1),
          3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        nst1 (Loop (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq (Loop' (Fin Nop) (Fin Nop)) (Envs' 1),
                     0, Nothing, [newEnv])

    -- loop-nop --
    describe "(Loop' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Loop Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' Nop (EmitInt 8), 3, Nothing, [newEnv])
        `shouldBe` (Loop (EmitInt 8), 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' Nop (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Loop (Fin Nop), 0, Nothing, [newEnv])

    -- loop-brk --
    describe "(Loop' Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' Break Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' Break (Seq (EmitInt 8) Nop), 3, Nothing, [newEnv])
        `shouldBe` (Nop, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' Break Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' Break (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

    -- loop-adv --
    describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' (Seq Nop Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Loop' Nop Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Loop' (Seq (EmitInt 8) Nop) Break, 3, Nothing, [newEnv])
        `shouldBe` (Loop' (Seq (CanRun 3) Nop) Break, 3, Just 8, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' (Seq Nop Nop) Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Loop' (Fin Nop) Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Loop' (Seq Nop Nop) (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Loop' Nop (Fin Nop), 0, Nothing, [newEnv])

    -- and-expd --
    describe "(And p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (And' Nop (Seq (CanRun 0) Nop), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, [newEnv])
        `shouldBe` (And' (Seq Nop (EmitInt 8))
                          (Seq (CanRun 3) (Seq Nop Nop)), 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And (Fin Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, Nothing, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And Nop (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (And' Nop (Seq (CanRun 0) (Fin Nop)),
                     0, Nothing, [newEnv])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (And (Fin Nop) (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
                     0, Nothing, [newEnv])

    -- and-nop1 --
    describe "(And' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And' Nop (EmitInt 8), 3, Nothing, [newEnv])
        `shouldBe` (EmitInt 8, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (And' Nop (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Fin Nop, 0, Nothing, [newEnv])

      it "pass: q == Nop" $
        nst1 (And' Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "pass: q == Break" $
        nst1 (And' Nop Break, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

    -- and-brk1 --
    describe "(And' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitExt 0) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0" $
        let q = (AwaitInt 0) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' Break q, 3, Nothing, [newEnv])
           `shouldBe` (Seq (clear q) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' Break (Var "x"), 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (And' Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4))))))
            clear_q = (Nop `Seq`
                       (EmitInt 1 `Seq`
                        ((EmitInt 2 `Seq` EmitInt 3) `Seq`
                         Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (And' Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (And' Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-nop2 --
    describe "(And' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        nst1 (And' (Fin Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Fin Nop, 0, Nothing, [newEnv])

      it "pass: lvl > 0 && isBlocked p" $
        nst1 (And' (Seq (Fin Nop) Nop) Nop, 3, Nothing, [newEnv])
        `shouldBe` (Seq (Fin Nop) Nop, 3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Fin Nop) Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: p == Nop" $
        nst1 (And' Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Nop, 0, Nothing, [newEnv])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-brk2 --
    describe "(And' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt 1) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (And' p Break, 0, Nothing, [newEnv])
           `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` (Seq Nop Nop))
          >>
          (nst1 (And' p Break, 3, Nothing, [newEnv])
           `shouldBe` (Seq (clear p) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Fin Nop) Break, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4))))))
            clear_p = (Nop `Seq`
                       (EmitInt 1 `Seq`
                        ((EmitInt 2 `Seq` EmitInt 3) `Seq`
                         Nop))) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' p Break, 0, Nothing, [newEnv])
            `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: p == Nop" $
        nst1 (And' Nop Break, 0, Nothing, [newEnv])
        `shouldBe` (Break, 0, Nothing, [newEnv])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- and-adv --
    describe "(And' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [newEnv])
        `shouldBe` (And' Nop (Seq Break Break), 0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (And' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop),
               3, Nothing, [newEnv])
        `shouldBe` (And' (Seq (CanRun 3) Nop) (Seq (EmitInt 9) Nop),
                     3, Just 8, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Seq Nop Nop) (Seq Nop Nop),
                         0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And' (Fin Nop) (Seq (EmitInt 8) Nop),
               3, Nothing, [newEnv])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 3) Nop),
                     3, Just 8, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And' (EmitInt 8) (AwaitInt 8), 3, Nothing, [newEnv])
        `shouldBe` (And' (CanRun 3) (AwaitInt 8), 3, Just 8, [newEnv])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (And' (AwaitInt 3) (AwaitInt 4),
                          0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    -- or-expd --
    describe "(Or p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or Nop Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) Nop)) (Envs' 1),
                     0, Nothing, [newEnv])

      it "pass: lvl > 0" $
        nst1 (Or (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, [newEnv])
        `shouldBe` (Seq (Or' (Seq Nop (EmitInt 8))
                          (Seq (CanRun 3) (Seq Nop Nop))) (Envs' 1),
                     3, Nothing, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or (Fin Nop) Nop, 0, Nothing, [newEnv])
        `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) Nop)) (Envs' 1),
                     0, Nothing, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or Nop (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) (Fin Nop))) (Envs' 1),
                     0, Nothing, [newEnv])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (Or (Fin Nop) (Fin Nop), 0, Nothing, [newEnv])
        `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)))
                     (Envs' 1), 0, Nothing, [newEnv])

    -- or-nop1 --
    describe "(Or' Nop q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt 0) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 0, Nothing, [newEnv])
           `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "pass: lvl > 0" $
        let q = (AwaitInt 8) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 3, Nothing, [newEnv])
           `shouldBe` (clear q, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' Nop Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = (Fin Nop) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 0, Nothing, [newEnv])
           `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4))))))
            clear_q = (Nop `Seq`
                       (EmitInt 1 `Seq`
                        ((EmitInt 2 `Seq` EmitInt 3) `Seq`
                         Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' Nop q, 0, Nothing, [newEnv])
            `shouldBe` (clear q, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-brk1 --
    describe "(Or' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt 0) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Break q, 0, Nothing, [newEnv])
           `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

      it "transit: lvl > 0" $
        let q = (AwaitInt 8) in
          (clear q`shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Break q, 3, Nothing, [newEnv])
           `shouldBe` (Seq (clear q) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' Break Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (Or' Break q, 0, Nothing, [newEnv])
           `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4))))))
            clear_q = (Nop `Seq`
                       (EmitInt 1 `Seq`
                        ((EmitInt 2 `Seq` EmitInt 3) `Seq`
                         Nop))) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' Break q, 0, Nothing, [newEnv])
            `shouldBe` (Seq clear_q Break, 0, Nothing, [newEnv]))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-nop2 --
    describe "(Or' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin Nop) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Nop, 0, Nothing, [newEnv])
            `shouldBe` (clear p, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq (Fin Nop) Nop in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Nop, 3, Nothing, [newEnv])
            `shouldBe` (clear p, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Fin Nop) Nop, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-brk2 --
    describe "(Or' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt 1) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Break, 0, Nothing, [newEnv])
           `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` Seq Nop Nop)
          >>                    -- clear p == Nop; Nop
          (nst1 (Or' p Break, 3, Nothing, [newEnv])
            `shouldBe` (Seq (clear p) Break, 3, Nothing, [newEnv]))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Fin Nop) Break, 0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = (Or' (Seq (AwaitExt 0) (Fin Nop))
                 (And' (Fin (EmitInt 1))
                  (Or' (Fin (Seq (EmitInt 2) (EmitInt 3)))
                    (Seq (AwaitInt 0) (Fin (EmitInt 4))))))
            clear_p = (Nop `Seq`
                       (EmitInt 1 `Seq`
                        ((EmitInt 2 `Seq` EmitInt 3) `Seq`
                         Nop))) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' p Break, 0, Nothing, [newEnv])
            `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Break, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "clear: invalid clear"

    -- or-adv --
    describe "(Or' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [newEnv])
        `shouldBe` (Or' Nop (Seq Break Break), 0, Nothing, [newEnv])

      it "psas: lvl > 0" $
        nst1 (Or' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop),
               3, Nothing, [newEnv])
        `shouldBe` (Or' (Seq (CanRun 3) Nop) (Seq (EmitInt 9) Nop),
                     3, Just 8, [newEnv])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Seq Nop Nop) (Seq Nop Nop),
                          0, Just 1, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, [newEnv])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, [newEnv])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or' (EmitInt 8) (AwaitInt 8), 3, Nothing, [newEnv])
        `shouldBe` (Or' (CanRun 3) (AwaitInt 8), 3, Just 8, [newEnv])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (Or' (AwaitInt 3) (AwaitInt 4),
                          0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- nsts ------------------------------------------------------------------
  describe "nsts" $ do
    describe "zero steps (program is blocked)" $ do
      it "pass: AwaitExt#" $
        let d = (AwaitExt 0, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: AwaitInt#" $
        let d = (AwaitInt 0, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: Seq#" $
        let d = (Seq (AwaitInt 0) Nop, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: Every#" $
        let d = (Every 0 Nop, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: Fin#" $
        let d = (Fin (Seq Nop Nop), 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: And'#" $
        let d = (And' (AwaitExt 0) (Fin Nop), 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: nsts Or'#" $
        let d = (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "fail: CanRun# (cannot advance)" $
        forceEval (nsts (CanRun 5, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "nst1: cannot advance"

    describe "zero steps (no nst1-rule applies)" $ do
      it "pass: Nop#" $
        let d = (Nop, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

      it "pass: Break#" $
        let d = (Break, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d) >> (isNstIrreducible d `shouldBe` True)

    describe "one+ steps" $ do
      it "pass: {var x; x=1} -> [] Nop#" $
        let d = (Block (Var "x" `Seq` (Write "x" (Const 0))),
                  3, Nothing, [newEnv])
            d' = (Nop, 3, Nothing, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: var x; x=1 -> [x=1] Nop#" $
        let d = (Var "x" `Seq` (Write "x" (Const 0)), 3, Nothing, [newEnv])
            d' = (Nop, 3, Nothing, [(["x"],[("x",0)])]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: EmitInt -> CanRun#" $
        let d = (EmitInt 8, 3, Nothing, [newEnv])
            d' = (CanRun 3, 3, Just 8, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: CanRun -> Nop#" $
        let d = (CanRun 3, 3, Nothing, [newEnv])
            d' = (Nop, 3, Nothing, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: Nop; Nop; Nop; Break; Nop -> Break#" $
        let p = Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop
            d = (p, 0, Nothing, [newEnv])
            d' = (Break, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: Loop Break; Nop; Nop; EmitInt; Break -> CanRun#; Break" $
        let p = Loop Break `Seq` Nop `Seq` Nop `Seq` EmitInt 8 `Seq` Break
            d = (p, 3, Nothing, [newEnv])
            d' = (Seq (CanRun 3) Break, 3, Just 8, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: (Loop Break; Nop) && (EmitInt; Nop) -> CanRun#; Nop" $
        let p = Seq (Loop Break) Nop `And` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, [newEnv])
            d' = (Seq (CanRun 3) Nop, 3, Just 8, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: (Loop Break; Nop) || (EmitInt; Nop) -> Nop#" $
        let p = Seq (Loop Break) Nop `Or` Seq (EmitInt 8) Nop
            d = (p, 3, Nothing, [newEnv])
            d' = (Nop, 3, Nothing, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

      it "pass: Loop ((Nop; AwaitInt) && (AwaitExt || Nop; Break)) -> Nop#" $
        let p = Loop ((Nop `Seq` AwaitInt 3)
                      `And` (AwaitExt 18 `Or` (Nop `Seq` Break)))
            d = (p, 0, Nothing, [newEnv])
            d' = (Nop, 0, Nothing, [newEnv]) in
          (nsts d `shouldBe` d') >> (isNstIrreducible d' `shouldBe` True)

  -- out1 ------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 (Nop, 0, Just 1, [newEnv])
        `shouldBe` (Nop, 1, Nothing, [newEnv])

      it "pass: lvl > 0" $
        out1 (Seq (AwaitInt 1) Break, 3, Just 1, [newEnv])
        `shouldBe` (Seq Nop Break, 4, Nothing, [newEnv])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt 2) Break, 3, Just 1, [newEnv])
        `shouldBe` (Seq (AwaitInt 2) Break, 4, Nothing, [newEnv])

    -- pop --
    describe "pop" $ do
      it "fail: lvl == 0 (cannot advance)" $
        forceEval (out1 (Nop, 0, Nothing, [newEnv]))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "pass: lvl > 0 && isNstIrreducible p" $
        out1 (Nop, 33, Nothing, [newEnv])
        `shouldBe` (Nop, 32, Nothing, [newEnv])

      it "pass: lvl > 0 && not (nstIrreducible p)" $
        forceEval (out1 (Seq Nop Nop, 1, Nothing, [newEnv]))
        `shouldThrow` errorCall "outPop: cannot advance"

  -- nsts_out1_s -----------------------------------------------------------
  describe "nsts_out1_s" $ do
    describe "zero steps (no out-rule applies)" $ do
      it "pass: lvl == 0 && isNstIrreducible p" $
        let d = (Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` True)
          >> (isIrreducible d `shouldBe` True)

      it "pass: lvl == 0 && not (isNstIrreducible p)" $
        let d = (Seq Nop Nop, 0, Nothing, [newEnv]) in
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
        let d = (AwaitInt 3, 0, Just 3, [newEnv])
            d' = (AwaitInt 3, 0, Just 3, [newEnv]) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          -- >> (isIrreducible d' `shouldBe` True)

      it "pass: lvl > 0" $
        let d = (AwaitInt 3, 88, Just 3, [newEnv])
            d' = (Nop, 0, Nothing, [newEnv]) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

  -- reaction --------------------------------------------------------------
  describe "reaction" $ do

    it "Nop; (AwaitInt 3) && Nop; Fin Nop -> Nop" $
      reaction ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` Fin Nop), 3, [([],[])])
      `shouldBe` (AwaitInt 3 `And'` Fin Nop, [([],[])])

    it "Nop; (AwaitInt 3) && Nop; (EmitInt 3) -> Nop" $
      reaction ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` EmitInt 3), 1, [([],[])])
      `shouldBe` (Nop, [([],[])])

  -- evalProg -----------------------------------------------------------------
  describe "evalProg" $ do

    it "var a; var ret; a=1; ret=a+10;" $
      let p = Seq (Var "a") (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10))))) in
        (evalProg p []) `shouldBe` 11

    it "var a; {var ret; a=1; ret=a+10;}" $
      let p = Seq (Var "a") (Block (Seq (Var "ret") (Seq (Write "a" (Const 1)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        forceEval (evalProg p [])
        `shouldThrow` errorCall "envsGet: undeclared variable"

    it "var ret; ret=1; {var ret; ret=99;}" $
      let p = Seq (Var "ret") (Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Seq (Var "ret") (Write "ret" (Const 99)))))) in
        (evalProg p []) `shouldBe` 1

    it "var ret; var a; a=1; {var a; a=99;} ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Block (Seq (Var "a") (Write "a" (Const 99)))) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p []) `shouldBe` 11

    it "var ret; ret=1; {ret=2;}" $
      let p = Seq (Var "ret") (Seq (Write "ret" (Const 1)) (Block (Write "ret" (Const 2)))) in
        (evalProg p []) `shouldBe` 2

    it "var ret; var a; a=1; ({var a; a=99; awaitExt E} || nop); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Or (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Nop) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p []) `shouldBe` 11

    it "var ret; ({ret=1; awaitExt E} || nop);" $
      let p = Seq (Var "ret") (Or (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Nop) in
        (evalProg p []) `shouldBe` 1

    it "var ret; var a; a=1; loop ({var a; a=99; awaitExt E} && break); ret=a+10;" $
      let p = Seq (Var "ret") (Seq (Var "a") (Seq (Write "a" (Const 1)) (Seq (Loop (And (Block (Seq (Var "a") (Seq (Write "a" (Const 99)) (AwaitExt 0)))) Break)) (Write "ret" (Add (Read "a") (Const 10)))))) in
        (evalProg p []) `shouldBe` 11

    it "var ret; loop ({ret=1; awaitExt E} && break);" $
      let p = Seq (Var "ret") (Loop (And (Block (Seq (Write "ret" (Const 1)) (AwaitExt 0))) Break))in
        (evalProg p []) `shouldBe` 1

    -- multiple inputs

    it "[0] | var ret; awaitExt 0; ret=1;" $
      let p = Seq (Var "ret") (Seq (AwaitExt 0) (Write "ret" (Const 1))) in
        (evalProg p [0]) `shouldBe` 1

    it "[] | var ret; awaitExt 0; ret=1;" $
      let p = Seq (Var "ret") (Seq (AwaitExt 0) (Write "ret" (Const 1))) in
        evaluate (evalProg p [])
        `shouldThrow` errorCall "evalProg: did not terminate"

    it "[1] | var ret; awaitExt 0; ret=1;" $
      let p = Seq (Var "ret") (Seq (AwaitExt 0) (Write "ret" (Const 1))) in
        evaluate (evalProg p [1])
        `shouldThrow` errorCall "evalProg: did not terminate"

    it "[0,0] | var ret; awaitExt 0; ret=1;" $
      let p = Seq (Var "ret") (Seq (AwaitExt 0) (Write "ret" (Const 1))) in
        evaluate (evalProg p [0,0])
        `shouldThrow` errorCall "evalProg: pending inputs"

    it "[0,1] | var ret; awaitExt 0; awaitExt 1; ret=1;" $
      let p = Seq (Var "ret") (Seq (AwaitExt 0) (Seq (AwaitExt 1) (Write "ret" (Const 1)))) in
        (evalProg p [0,1]) `shouldBe` 1
