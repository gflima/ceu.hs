module Ceu.EvalSpec (main, spec) where

import Ceu.Eval
import Ceu.Grammar
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Expr, Stmt, and Desc as datatypes that can be fully evaluated.
instance NFData Expr where
  rnf (Const _)   = ()
  rnf (Read _)    = ()
  rnf (Umn e)     = rnf e
  rnf (Add e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Sub e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Mul e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Div e1 e2) = rnf e1 `deepseq` rnf e2

instance NFData Stmt where
  rnf (Local _ p)      = rnf p
  rnf (Write var expr) = rnf expr
  rnf (AwaitExt _)     = ()
  rnf (AwaitInt _)     = ()
  rnf (EmitInt _)      = ()
  rnf (Break)          = ()
  rnf (If expr p q)    = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq p q)        = rnf p `deepseq` rnf q
  rnf (Loop p)         = rnf p
  rnf (Every _ p)      = rnf p
  rnf (And p q)        = rnf p `deepseq` rnf q
  rnf (Or p q)         = rnf p `deepseq` rnf q
  rnf (Fin p)          = rnf p
  rnf (Nop)            = ()
  rnf (Error _)        = ()
  rnf (CanRun _)       = ()
  rnf (Local' _ _ p)   = rnf p
  rnf (Loop' p q)      = rnf p
  rnf (And' p q)       = rnf p `deepseq` rnf q
  rnf (Or' p q)        = rnf p `deepseq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  -- describe "Env/Envs" $ do

  -- TODO: *** UPDATE ***

  --   describe "envsGet envs id" $ do
  --     it "fail: envs == [] (bad environment)" $
  --       forceEval (envsGet [] "x")
  --       `shouldThrow` errorCall "envsGet: bad environment"

  --     it "fail: undeclared variable" $
  --       forceEval (envsGet [newEnv] "x")
  --       `shouldThrow` errorCall "envsGet: undeclared variable: x"

  --     it "pass: find in simple env" $
  --       envsGet [(["x"],[("x",0)])] "x" -- CHECK THIS! --
  --       `shouldBe` ([],(["x"],[("x",0)]),[])

  --     it "pass: find in complex env" $
  --       let envs = [(["z"],[]),
  --                   (["y"],[("y",1)]),
  --                   (["y"],[("y",0)]),
  --                   (["x"],[])] in
  --         envsGet envs "y"
  --         `shouldBe` ([(["z"],[])],
  --                     (["y"],[("y",1)]),
  --                     [(["y"],[("y",0)]),(["x"],[])])

  --   describe "envsWrite envs id val" $ do
  --     it "fail: envs == [] (bad environment)" $
  --       forceEval (envsWrite [] "x" 0)
  --       `shouldThrow` errorCall "envsGet: bad environment"

  --     it "fail: undeclared variable" $
  --       forceEval (envsWrite [newEnv] "x" 0)
  --       `shouldThrow` errorCall "envsGet: undeclared variable: x"

  --     it "pass: 1st write" $
  --       envsWrite [(["x"],[])] "x" 0 `shouldBe` [(["x"],[("x",0)])]

  --     it "pass: 2st write" $
  --       envsWrite [(["x"],[("x",0)])] "x" 1
  --       `shouldBe` [(["x"],[("x",1),("x",0)])]

  --     it "pass: 1st write in inner env" $
  --       envsWrite [newEnv,(["x"],[]),(["x"],[("x",0)])] "x" 1
  --       `shouldBe` [newEnv,(["x"],[("x",1)]),(["x"],[("x",0)])]

  --     it "pass: 2nd write in inner env" $
  --       envsWrite [newEnv,(["x"],[("x",1)]),(["x"],[("x",0)])] "x" 2
  --       `shouldBe` [newEnv,(["x"],[("x",2),("x",1)]),(["x"],[("x",0)])]

  --   describe "envsRead envs id" $ do
  --     it "fail: envs == [] (bad environment)" $
  --       forceEval (envsRead [] "x")
  --       `shouldThrow` errorCall "envsGet: bad environment"

  --     it "fail: undeclared variable" $
  --       forceEval (envsRead [newEnv] "x")
  --       `shouldThrow` errorCall "envsGet: undeclared variable: x"

  --     it "fail: uninitialized variable" $
  --       forceEval (envsRead [(["x"],[])] "x")
  --       `shouldThrow` errorCall "envsRead: uninitialized variable: x"

  --     it "pass: read in simple env" $
  --       envsRead [(["x"],[("x",0)])] "x" `shouldBe` 0

  --     it "pass: read in complex env" $
  --       let envs = [newEnv,
  --                   (["y"],[]),
  --                   (["y","x"],[("y",1),("y",0),("x",1),("x",0)]),
  --                   (["x"],[("x",99)])] in
  --         envsRead envs "x" `shouldBe` 1

  --   describe "envsEval envs exp" $ do
  --     it "pass: envs == [] && exp == (Const _)" $
  --       envsEval [] (Const 0) `shouldBe` 0 -- CHECK THIS! --

  --     it "fail: envs == [] && exp != (Const _) (bad environment)" $
  --       forceEval (envsEval [] (Read "x"))
  --       `shouldThrow` errorCall "envsGet: bad environment"

  --     it "fail: undeclared variable" $
  --       forceEval (envsEval [newEnv] (Read "x"))
  --       `shouldThrow` errorCall "envsGet: undeclared variable: x"

  --     it "fail: uninitialized variable" $
  --       forceEval (envsEval [(["x"],[])] (Read "x"))
  --       `shouldThrow` errorCall "envsRead: uninitialized variable: x"

  --     it "pass: eval in simple env" $
  --       let envs = [(["x","y"],[("x",1),("y",2)])] in
  --         envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
  --         `shouldBe` (-4)

  --     it "pass: eval in complex env" $
  --       let envs = [(["y"],[("y",2)]),
  --                   (["y","x"],[("y",0),("x",1)]),
  --                    (["x"],[("x",0)])] in
  --         envsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
  --         `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "nst1" $ do

    -- error --
    describe "(Error \"erro\")" $ do
      it "fail: error \"erro\"" $
        (forceEval $ nst1 (Error "erro", 0, Nothing, []))
        `shouldThrow` errorCall "Runtime error: erro"

    -- block --
    describe "(Local \"x\" p)" $ do
      it "pass: Local \"x\" Nop" $
        nst1 (Local "x" Nop, 0, Nothing, [])
        `shouldBe` (Local' "x" Nothing Nop, 0, Nothing, [])

      it "pass: Local [\"x\"] p" $
        nst1 (Local "x" (Seq Nop Nop), 0, Nothing, [])
        `shouldBe` (Local' "x" Nothing (Seq Nop Nop), 0, Nothing, [])

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        (forceEval $ nst1 (Write "x" (Read "y"), 0, Nothing, []))
        `shouldThrow` errorCall "envWrite: no such variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        (forceEval $ nst1 (Write "x" (Const 1), 0, Nothing, []))
        `shouldThrow` errorCall "envWrite: no such variable: x"

      it "pass: [x=?] x=1" $
        nst1 (Local' "x" Nothing (Write "x" (Const 1)), 0, Nothing, [])
        `shouldBe` (Local' "x" (Just 1) Nop, 0, Nothing, [])

      it "pass: [x=1] x=2" $
        nst1 (Local' "x" (Just 1) (Write "x" (Const 2)), 0, Nothing, [])
        `shouldBe` (Local' "x" (Just 2) Nop, 0, Nothing, [])

      it "fail: [x=?,y=?] x=y (uninitialized variable)" $
        let p = Local' "x" (Just 1)
               (Local' "y" Nothing
                 (Write "x" (Read "y"))) in
          (forceEval $ nst1 (p, 0, Nothing, []))
          `shouldThrow` errorCall "envRead: uninitialized variable: y"

      it "pass: nop; x=1" $
        nst1
        (Local' "x" Nothing
          (Nop `Seq` (Write "x" (Const 1))), 0, Nothing, [])
        `shouldBe`
        (Local' "x" Nothing
          (Write "x" (Const 1)), 0, Nothing, [])

      it "fail: [x=1] y=x+2 (undeclared variable)" $
        (forceEval $ nst1
          (Local' "x" (Just 1)
          (Local' "y" Nothing
            (Write "y" (Read "x" `Add` Const 2))), 0, Nothing, []))
        `shouldThrow` errorCall "envsGet: undeclared variable: y"

      it "pass: [x=1,y=?] y=x+2" $
        nst1
        (Local' "x" (Just 1)
        (Local' "y" Nothing
          (Write "y" (Read "x" `Add` Const 2))), 0, Nothing, [])
        `shouldBe`
        (Local' "x" (Just 1)
        (Local' "y" (Just 3) Nop), 0, Nothing, [])

      it "pass: [x=?] x=-(5+1)" $
        nst1
        (Local' "x" (Just 0)
          (Write "x" (Umn (Const 5 `Add` Const 1))), 0, Nothing, [])
        `shouldBe`
        (Local' "x" (Just (-6)) Nop, 0, Nothing, [])

  --   -- emit-int --
  --   describe "(EmitInt e')" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (EmitInt 0, 0, Nothing, [newEnv])
  --       `shouldBe` (CanRun 0, 0, Just 0, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (EmitInt 1, 3, Nothing, [newEnv])
  --       `shouldBe` (CanRun 3, 3, Just 1, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (EmitInt 1, 3, Just 1, [([],[])]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- can-run --
  --   describe "(CanRun n)" $ do
  --     it "pass: n == lvl" $
  --       nst1 (CanRun 0, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "pass: n == lvl" $
  --       nst1 (CanRun 8, 8, Nothing, [newEnv])
  --       `shouldBe` (Nop, 8, Nothing, [newEnv])

  --     it "fail: n > lvl (cannot advance)" $
  --       forceEval (nst1 (CanRun 8, 6, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: n < lvl (cannot advance)" $
  --       forceEval (nst1 (CanRun 8, 12, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (CanRun 0, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- seq-nop --
  --   describe "(Seq Nop q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Seq Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Seq Nop Break, 3, Nothing, [newEnv])
  --       `shouldBe` (Break, 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Seq Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- seq-brk --
  --   describe "(Seq Break q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Seq Break Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Break, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Seq Break (EmitInt 8), 3, Nothing, [newEnv])
  --       `shouldBe` (Break, 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Seq Break Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- seq-adv --
  --   describe "(Seq p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Seq (Seq Nop Nop) Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Seq Nop Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Seq (Seq (EmitInt 8) Nop) Nop, 3, Nothing, [newEnv])
  --       `shouldBe` (Seq (Seq (CanRun 3) Nop) Nop, 3, Just 8, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Seq (Seq Nop Nop) Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: isBlocked p (cannot advance)" $
  --       forceEval (nst1 (Seq (Fin Nop) Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- if-true/false --
  --   describe "(If exp p q)" $ do
  --     it "fail: undeclared variable" $
  --       forceEval (nst1 (If (Read "x") Nop Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "envsGet: undeclared variable: x"

  --     it "pass: x == 0" $
  --       nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",0)])])
  --       `shouldBe` (Break, 0, Nothing, [(["x"],[("x",0)])])

  --     it "pass: x /= 0" $
  --       nst1 (If (Read "x") Nop Break, 0, Nothing, [(["x"],[("x",1)])])
  --       `shouldBe` (Nop, 0, Nothing, [(["x"],[("x",1)])])

  --   -- loop-expd --
  --   describe "(Loop p)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Loop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Loop' Nop Nop) (Restore 1), 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Loop (Seq Nop (EmitInt 8)), 3, Nothing, [newEnv])
  --       `shouldBe`
  --       (Seq (Loop' (Seq Nop (EmitInt 8)) (Seq Nop (EmitInt 8)))
  --            (Restore 1),
  --         3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Loop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: isBlocked p (cannot advance)" $
  --       nst1 (Loop (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Loop' (Fin Nop) (Fin Nop)) (Restore 1),
  --                    0, Nothing, [newEnv])

  --   -- loop-nop --
  --   describe "(Loop' Nop q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Loop' Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Loop Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Loop' Nop (EmitInt 8), 3, Nothing, [newEnv])
  --       `shouldBe` (Loop (EmitInt 8), 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Loop' Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       nst1 (Loop' Nop (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Loop (Fin Nop), 0, Nothing, [newEnv])

  --   -- loop-brk --
  --   describe "(Loop' Break q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Loop' Break Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Loop' Break (Seq (EmitInt 8) Nop), 3, Nothing, [newEnv])
  --       `shouldBe` (Nop, 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Loop' Break Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       nst1 (Loop' Break (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --   -- loop-adv --
  --   describe "(Loop' p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Loop' (Seq Nop Nop) Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Loop' Nop Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Loop' (Seq (EmitInt 8) Nop) Break, 3, Nothing, [newEnv])
  --       `shouldBe` (Loop' (Seq (CanRun 3) Nop) Break, 3, Just 8, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Loop' (Seq Nop Nop) Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: isBlocked p (cannot advance)" $
  --       forceEval (nst1 (Loop' (Fin Nop) Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: not (isBlocked p) && isBlocked q" $
  --       nst1 (Loop' (Seq Nop Nop) (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Loop' Nop (Fin Nop), 0, Nothing, [newEnv])

  --   -- and-expd --
  --   describe "(And p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (And Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (And' Nop (Seq (CanRun 0) Nop), 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (And (Nop `Seq` EmitInt 8)  (Nop `Seq` Nop),
  --              3, Nothing, [newEnv])
  --       `shouldBe` (And' (Nop `Seq` EmitInt 8)
  --                    (CanRun 3 `Seq` Nop `Seq` Nop), 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p && not (isBlocked q)" $
  --       nst1 (And (Fin Nop) Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) Nop),
  --                    0, Nothing, [newEnv])

  --     it "pass: not (isBlocked p) && isBlocked q" $
  --       nst1 (And Nop (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (And' Nop (Seq (CanRun 0) (Fin Nop)),
  --                    0, Nothing, [newEnv])

  --     it "pass: isBlocked p && isBlocked q" $
  --       nst1 (And (Fin Nop) (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
  --                    0, Nothing, [newEnv])

  --   -- and-nop1 --
  --   describe "(And' Nop q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (And' Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (And' Nop (EmitInt 8), 3, Nothing, [newEnv])
  --       `shouldBe` (EmitInt 8, 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And' Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       nst1 (And' Nop (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Fin Nop, 0, Nothing, [newEnv])

  --     it "pass: q == Nop" $
  --       nst1 (And' Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "pass: q == Break" $
  --       nst1 (And' Nop Break, 0, Nothing, [newEnv])
  --       `shouldBe` (Break, 0, Nothing, [newEnv])

  --   -- and-brk1 --
  --   describe "(And' Break q)" $ do
  --     it "pass: lvl == 0" $
  --       let q = (AwaitExt 0) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (And' Break q, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

  --     it "pass: lvl > 0" $
  --       let q = (AwaitInt 0) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (And' Break q, 3, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear q) Break, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And' Break (Block [] Nop), 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       let q = Fin (Seq Nop Nop) in
  --         (clear q `shouldBe` (Seq Nop Nop))
  --         >>                    -- clear q == Nop; Nop
  --         (nst1 (And' Break q, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

  --     it "pass: isBlocked q (nontrivial clear)" $
  --       let q = Or' (AwaitExt 0 `Seq` Fin Nop)
  --                   (And' (Fin (EmitInt 1))
  --                         (Or' (Fin (EmitInt 2 `Seq` EmitInt 3))
  --                           (AwaitInt 0 `Seq` Fin (EmitInt 4))))
  --           clear_q = Nop `Seq` EmitInt 1 `Seq`
  --                     (EmitInt 2 `Seq` EmitInt 3) `Seq` Nop in
  --         (clear q `shouldBe` clear_q)
  --         >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
  --         (nst1 (And' Break q, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

  --     it "fail: q == Nop (invalid clear)" $
  --       forceEval (nst1 (And' Break Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --     it "fail: q == Break (invalid clear)" $
  --       forceEval (nst1 (And' Break Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- and-nop2 --
  --   describe "(And' p Nop)" $ do
  --     it "pass: lvl == 0 && isBlocked p" $
  --       nst1 (And' (Fin Nop) Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Fin Nop, 0, Nothing, [newEnv])

  --     it "pass: lvl > 0 && isBlocked p" $
  --       nst1 (And' (Seq (Fin Nop) Nop) Nop, 3, Nothing, [newEnv])
  --       `shouldBe` (Seq (Fin Nop) Nop, 3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And' (Fin Nop) Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: p == Nop" $
  --       nst1 (And' Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Nop, 0, Nothing, [newEnv])

  --     it "fail: p == Break (invalid clear)" $
  --       forceEval (nst1 (And' Break Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- and-brk2 --
  --   describe "(And' p Break)" $ do
  --     it "pass: lvl == 0 && isBlocked p" $
  --       let p = (AwaitInt 1) in
  --         (clear p `shouldBe` Nop)
  --         >>                    -- clear p == Nop
  --         (nst1 (And' p Break, 0, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

  --     it "pass: lvl > 0 && isBlocked p" $
  --       let p = Fin (Seq Nop Nop) in
  --         (clear p `shouldBe` (Seq Nop Nop))
  --         >>
  --         (nst1 (And' p Break, 3, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear p) Break, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And' (Fin Nop) Break, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p (nontrivial clear)" $
  --       let p = Or' (AwaitExt 0 `Seq` Fin Nop)
  --                   (And' (Fin (EmitInt 1))
  --                         (Or' (Fin (EmitInt 2 `Seq` EmitInt 3))
  --                           (AwaitInt 0 `Seq` Fin (EmitInt 4))))
  --           clear_p = Nop `Seq` EmitInt 1 `Seq`
  --                     (EmitInt 2 `Seq` EmitInt 3) `Seq` Nop in
  --         (clear p `shouldBe` clear_p)
  --         >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
  --         (nst1 (And' p Break, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

  --     it "pass: p == Nop" $
  --       nst1 (And' Nop Break, 0, Nothing, [newEnv])
  --       `shouldBe` (Break, 0, Nothing, [newEnv])

  --     it "fail: p == Break (invalid clear)" $
  --       forceEval (nst1 (And' Break Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- and-adv --
  --   describe "(And' p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (And' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [newEnv])
  --       `shouldBe` (And' Nop (Seq Break Break), 0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (And' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop),
  --              3, Nothing, [newEnv])
  --       `shouldBe` (And' (Seq (CanRun 3) Nop) (Seq (EmitInt 9) Nop),
  --                    3, Just 8, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (And' (Seq Nop Nop) (Seq Nop Nop),
  --                        0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p && not (isBlocked q)" $
  --       nst1 (And' (Fin Nop) (Seq (EmitInt 8) Nop),
  --              3, Nothing, [newEnv])
  --       `shouldBe` (And' (Fin Nop) (Seq (CanRun 3) Nop),
  --                    3, Just 8, [newEnv])

  --     it "pass: not (isBlocked p) && isBlocked q" $
  --       nst1 (And' (EmitInt 8) (AwaitInt 8), 3, Nothing, [newEnv])
  --       `shouldBe` (And' (CanRun 3) (AwaitInt 8), 3, Just 8, [newEnv])

  --     it "fail: isBlocked p && isBlocked q (cannot advance)" $
  --       forceEval (nst1 (And' (AwaitInt 3) (AwaitInt 4),
  --                         0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --   -- or-expd --
  --   describe "(Or p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Or Nop Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) Nop)) (Restore 1),
  --                    0, Nothing, [newEnv])

  --     it "pass: lvl > 0" $
  --       nst1 (Or (Seq Nop (EmitInt 8)) (Seq Nop Nop), 3, Nothing, [newEnv])
  --       `shouldBe` (Seq (Or' (Seq Nop (EmitInt 8))
  --                         (Seq (CanRun 3) (Seq Nop Nop))) (Restore 1),
  --                    3, Nothing, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p && not (isBlocked q)" $
  --       nst1 (Or (Fin Nop) Nop, 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) Nop)) (Restore 1),
  --                    0, Nothing, [newEnv])

  --     it "pass: not (isBlocked p) && isBlocked q" $
  --       nst1 (Or Nop (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Or' Nop (Seq (CanRun 0) (Fin Nop))) (Restore 1),
  --                    0, Nothing, [newEnv])

  --     it "pass: isBlocked p && isBlocked q" $
  --       nst1 (Or (Fin Nop) (Fin Nop), 0, Nothing, [newEnv])
  --       `shouldBe` (Seq (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)))
  --                    (Restore 1), 0, Nothing, [newEnv])

  --   -- or-nop1 --
  --   describe "(Or' Nop q)" $ do
  --     it "pass: lvl == 0" $
  --       let q = (AwaitInt 0) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (Or' Nop q, 0, Nothing, [newEnv])
  --          `shouldBe` (clear q, 0, Nothing, [newEnv]))

  --     it "pass: lvl > 0" $
  --       let q = (AwaitInt 8) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (Or' Nop q, 3, Nothing, [newEnv])
  --          `shouldBe` (clear q, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or' Nop Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       let q = (Fin Nop) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (Or' Nop q, 0, Nothing, [newEnv])
  --          `shouldBe` (clear q, 0, Nothing, [newEnv]))

  --     it "pass: isBlocked q (nontrivial clear)" $
  --       let q = Or' (AwaitExt 0 `Seq` Fin Nop)
  --                   (And' (Fin (EmitInt 1))
  --                         (Or' (Fin (EmitInt 2 `Seq` EmitInt 3))
  --                           (AwaitInt 0 `Seq` Fin (EmitInt 4))))
  --           clear_q = Nop `Seq` EmitInt 1 `Seq`
  --                     (EmitInt 2 `Seq` EmitInt 3) `Seq` Nop in
  --         (clear q `shouldBe` clear_q)
  --         >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
  --         (nst1 (Or' Nop q, 0, Nothing, [newEnv])
  --           `shouldBe` (clear q, 0, Nothing, [newEnv]))

  --     it "fail: q == Nop (invalid clear)" $
  --       forceEval (nst1 (Or' Nop Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --     it "fail: q == Break (invalid clear)" $
  --       forceEval (nst1 (Or' Nop Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- or-brk1 --
  --   describe "(Or' Break q)" $ do
  --     it "pass: lvl == 0" $
  --       let q = (AwaitInt 0) in
  --         (clear q `shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (Or' Break q, 0, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

  --     it "transit: lvl > 0" $
  --       let q = (AwaitInt 8) in
  --         (clear q`shouldBe` Nop)
  --         >>                    -- clear q == Nop
  --         (nst1 (Or' Break q, 3, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear q) Break, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or' Break Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked q" $
  --       let q = Fin (Seq Nop Nop) in
  --         (clear q `shouldBe` (Seq Nop Nop))
  --         >>                    -- clear q == Nop; Nop
  --         (nst1 (Or' Break q, 0, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear q) Break, 0, Nothing, [newEnv]))

  --     it "pass: isBlocked q (nontrivial clear)" $
  --       let q = Or' (AwaitExt 0 `Seq` Fin Nop)
  --                   (And' (Fin (EmitInt 1))
  --                         (Or' (Fin (EmitInt 2 `Seq` EmitInt 3))
  --                           (AwaitInt 0 `Seq` Fin (EmitInt 4))))
  --           clear_q = Nop `Seq` EmitInt 1 `Seq`
  --                     (EmitInt 2 `Seq` EmitInt 3) `Seq` Nop in
  --         (clear q `shouldBe` clear_q)
  --         >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
  --         (nst1 (Or' Break q, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq clear_q Break, 0, Nothing, [newEnv]))

  --     it "fail: q == Nop (invalid clear)" $
  --       forceEval (nst1 (Or' Break Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --     it "fail: q == Break (invalid clear)" $
  --       forceEval (nst1 (Or' Break Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- or-nop2 --
  --   describe "(Or' p Nop)" $ do
  --     it "pass: lvl == 0 && isBlocked p" $
  --       let p = (Fin Nop) in
  --         (clear p `shouldBe` Nop)
  --         >>                    -- clear p == Nop
  --         (nst1 (Or' p Nop, 0, Nothing, [newEnv])
  --           `shouldBe` (clear p, 0, Nothing, [newEnv]))

  --     it "pass: lvl > 0 && isBlocked p" $
  --       let p = Seq (Fin Nop) Nop in
  --         (clear p `shouldBe` Nop)
  --         >>                    -- clear p == Nop
  --         (nst1 (Or' p Nop, 3, Nothing, [newEnv])
  --           `shouldBe` (clear p, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or' (Fin Nop) Nop, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "fail: p == Nop (invalid clear)" $
  --       forceEval (nst1 (Or' Nop Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --     it "fail: p == Break (invalid clear)" $
  --       forceEval (nst1 (Or' Break Nop, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- or-brk2 --
  --   describe "(Or' p Break)" $ do
  --     it "pass: lvl == 0 && isBlocked p" $
  --       let p = (AwaitInt 1) in
  --         (clear p `shouldBe` Nop)
  --         >>                    -- clear p == Nop
  --         (nst1 (Or' p Break, 0, Nothing, [newEnv])
  --          `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

  --     it "pass: lvl > 0 && isBlocked p" $
  --       let p = Fin (Seq Nop Nop) in
  --         (clear p `shouldBe` Seq Nop Nop)
  --         >>                    -- clear p == Nop; Nop
  --         (nst1 (Or' p Break, 3, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear p) Break, 3, Nothing, [newEnv]))

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or' (Fin Nop) Break, 0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p (nontrivial clear)" $
  --       let p = Or' (AwaitExt 0 `Seq` Fin Nop)
  --                   (And' (Fin (EmitInt 1))
  --                         (Or' (Fin (EmitInt 2 `Seq` EmitInt 3))
  --                           (AwaitInt 0 `Seq` Fin (EmitInt 4))))
  --           clear_p = Nop `Seq` EmitInt 1 `Seq`
  --                     (EmitInt 2 `Seq` EmitInt 3) `Seq` Nop in
  --         (clear p `shouldBe` clear_p)
  --         >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
  --         (nst1 (Or' p Break, 0, Nothing, [newEnv])
  --           `shouldBe` (Seq (clear p) Break, 0, Nothing, [newEnv]))

  --     it "fail: p == Nop (invalid clear)" $
  --       forceEval (nst1 (Or' Nop Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --     it "fail: p == Break (invalid clear)" $
  --       forceEval (nst1 (Or' Break Break, 0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "clear: invalid clear"

  --   -- or-adv --
  --   describe "(Or' p q)" $ do
  --     it "pass: lvl == 0" $
  --       nst1 (Or' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [newEnv])
  --       `shouldBe` (Or' Nop (Seq Break Break), 0, Nothing, [newEnv])

  --     it "psas: lvl > 0" $
  --       nst1 (Or' (Seq (EmitInt 8) Nop) (Seq (EmitInt 9) Nop),
  --              3, Nothing, [newEnv])
  --       `shouldBe` (Or' (Seq (CanRun 3) Nop) (Seq (EmitInt 9) Nop),
  --                    3, Just 8, [newEnv])

  --     it "fail: evt /= nil (cannot advance)" $
  --       forceEval (nst1 (Or' (Seq Nop Nop) (Seq Nop Nop),
  --                         0, Just 1, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --     it "pass: isBlocked p && not (isBlocked q)" $
  --       nst1 (Or' (Fin Nop) (Seq (EmitInt 8) Nop), 3, Nothing, [newEnv])
  --       `shouldBe` (Or' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just 8, [newEnv])

  --     it "pass: not (isBlocked p) && isBlocked q" $
  --       nst1 (Or' (EmitInt 8) (AwaitInt 8), 3, Nothing, [newEnv])
  --       `shouldBe` (Or' (CanRun 3) (AwaitInt 8), 3, Just 8, [newEnv])

  --     it "fail: isBlocked p && isBlocked q (cannot advance)" $
  --       forceEval (nst1 (Or' (AwaitInt 3) (AwaitInt 4),
  --                         0, Nothing, [newEnv]))
  --       `shouldThrow` errorCall "nst1: cannot advance"

  --------------------------------------------------------------------------
  describe "nsts" $ do
    describe "zero steps (program is blocked)" $ do

      nstsItPass
        (AwaitExt 0, 0, Nothing, [])
        (AwaitExt 0, 0, Nothing, [])

      nstsItPass
        (AwaitInt 0, 0, Nothing, [])
        (AwaitInt 0, 0, Nothing, [])

      nstsItPass
        (Seq (AwaitInt 0) Nop, 0, Nothing, [])
        (Seq (AwaitInt 0) Nop, 0, Nothing, [])

      nstsItPass
        (Every 0 Nop, 0, Nothing, [])
        (Every 0 Nop, 0, Nothing, [])

      nstsItPass
        (Fin (Seq Nop Nop), 0, Nothing, [])
        (Fin (Seq Nop Nop), 0, Nothing, [])

      nstsItPass
        (And' (AwaitExt 0) (Fin Nop), 0, Nothing, [])
        (And' (AwaitExt 0) (Fin Nop), 0, Nothing, [])

      nstsItPass
        (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, [])
        (Or' (AwaitExt 0) (Fin Nop), 0, Nothing, [])

      nstsItFail "nst1: cannot advance"
        (CanRun 5, 0, Nothing, [])

    describe "zero steps (no nst1-rule applies)" $ do

      nstsItPass
        (Nop, 0, Nothing, [])
        (Nop, 0, Nothing, [])

      nstsItPass
        (Break, 0, Nothing, [])
        (Break, 0, Nothing, [])

    describe "one+ steps" $ do

      nstsItPass
        (Local "x" (Write "x" (Const 0)), 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (EmitInt 8, 3, Nothing, [])
        (CanRun 3, 3, Just 8, [])

      nstsItPass
        (CanRun 3, 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop, 0, Nothing, [])
        (Break, 0, Nothing, [])

      nstsItPass
        (Loop Break `Seq` Nop `Seq` Nop `Seq` EmitInt 8 `Seq` Break,
          3, Nothing, [])
        (Seq (CanRun 3) Break, 3, Just 8, [])

      nstsItPass
        (Seq (Loop Break) Nop `And` Seq (EmitInt 8) Nop, 3, Nothing, [])
        (Seq (CanRun 3) Nop, 3, Just 8, [])

      nstsItPass
        (Seq (Loop Break) Nop `Or` Seq (EmitInt 8) Nop, 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (Loop
          ((Nop `Seq` AwaitInt 3) `And`
            (AwaitExt 18 `Or` (Nop `Seq` Break))), 0, Nothing, [])
        (Nop, 0, Nothing, [])

  --------------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 (Nop, 0, Just 1, [])
        `shouldBe` (Nop, 1, Nothing, [])

      it "pass: lvl > 0" $
        out1 (Seq (AwaitInt 1) Break, 3, Just 1, [])
        `shouldBe` (Seq Nop Break, 4, Nothing, [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt 2) Break, 3, Just 1, [])
        `shouldBe` (Seq (AwaitInt 2) Break, 4, Nothing, [])

    -- pop --
    describe "pop" $ do
      it "fail: lvl == 0 (cannot advance)" $
        forceEval (out1 (Nop, 0, Nothing, []))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "pass: lvl > 0 && isNstIrreducible p" $
        out1 (Nop, 33, Nothing, [])
        `shouldBe` (Nop, 32, Nothing, [])

      it "pass: lvl > 0 && not (nstIrreducible p)" $
        forceEval (out1 (Seq Nop Nop, 1, Nothing, []))
        `shouldThrow` errorCall "outPop: cannot advance"

  --------------------------------------------------------------------------
  describe "nsts_out1_s" $ do
    describe "zero steps (no out-rule applies)" $ do
      it "pass: lvl == 0 && isNstIrreducible p" $
        let d = (Nop, 0, Nothing, []) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` True)
          >> (isIrreducible d `shouldBe` True)

      it "pass: lvl == 0 && not (isNstIrreducible p)" $
        let d = (Seq Nop Nop, 0, Nothing, []) in
          (nsts_out1_s d `shouldBe` d)
          >> (isNstIrreducible d `shouldBe` False)
          >> (isIrreducible d `shouldBe` False)

    describe "one+ pops" $ do
      it "pass: lvl > 0" $
        let d = (Nop, 13, Nothing, [])
            d' = (Nop, 0, Nothing, []) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

    describe "one push followed by one+ pops" $ do
      it "pass: lvl == 0 (do nothing)" $ -- CHECK THIS! --
        let d = (AwaitInt 3, 0, Just 3, [])
            d' = (AwaitInt 3, 0, Just 3, []) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          -- >> (isIrreducible d' `shouldBe` True)

      it "pass: lvl > 0" $
        let d = (AwaitInt 3, 88, Just 3, [])
            d' = (Nop, 0, Nothing, []) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` Fin Nop), 3, [])
      (AwaitInt 3 `And'` Fin Nop, [])

    reactionItPass
      ((Nop `Seq` AwaitInt 3) `And` (Nop `Seq` EmitInt 3), 1, [])
      (Nop, [])

  --------------------------------------------------------------------------
  describe "evalProg" $ do

    evalProgItPass 11
      [] (Local "a"
           (Write "a" (Const 1) `Seq`
            Write "ret" (Read "a" `Add` Const 10)))

    evalProgItFail "evalProg: no return"
      [] (Local "a"
           (Local "ret"
             (Write "a" (Const 1) `Seq`
              Write "ret" (Read "a" `Add` Const 10))))

    evalProgItPass 1
      [] (Write "ret" (Const 1) `Seq`
          Local "ret" (Write "ret" (Const 99)))

    evalProgItPass 11
      [] (Local "a"
           (Write "a" (Const 1) `Seq`
            Local "a" (Write "a" (Const 99)) `Seq`
            Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 2
      [] (Write "ret" (Const 1) `Seq`
          Local "x" (Write "ret" (Const 2)))

    evalProgItPass 11
      [] (Local "a"
           (Write "a" (Const 1) `Seq`
            Or
             (Local "a" (Write "a" (Const 99) `Seq` AwaitExt 0))
             (Nop) `Seq`
           Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (Or
           (Local "x" (Write "ret" (Const 1) `Seq` AwaitExt 0))
           (Nop))

    evalProgItPass 11
      [] (Local "a"
           (Write "a" (Const 1) `Seq`
            Loop (And
                  (Local "a" (Write "a" (Const 99) `Seq` AwaitExt 0))
                  (Break)) `Seq`
             Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (Loop (And
                 (Local "x" (Write "ret" (Const 1) `Seq` AwaitExt 0))
                 (Break)))

    evalProgItPass 5 [] (
      (Write "ret" (Const 1)) `Seq`
      (And
        ((AwaitInt 0) `Seq` (Write "ret" (Const 5)))
        (EmitInt 0)
      ))

    evalProgItPass 5 [] (
      (Write "ret" (Const 1)) `Seq`
      (Or
        ((AwaitInt 0) `Seq` (Write "ret" (Const 5)))
        (Or (Fin (EmitInt 0)) Nop)
      ))

    -- multiple inputs

    evalProgItPass 1
      [0] (AwaitExt 0 `Seq` Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      [] (AwaitExt 0 `Seq` Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      [1] (AwaitExt 0 `Seq` Write "ret" (Const 1))

    evalProgItFail "evalProg: pending inputs"
      [0,0] (AwaitExt 0 `Seq` Write "ret" (Const 1))

    evalProgItPass 1
      [0,1] (AwaitExt 0 `Seq` AwaitExt 1 `Seq` Write "ret" (Const 1))

    evalProgItPass 1 [] (Write "ret" (Const 1))

      where
        nstsItPass (p,n,e,envs) (p',n',e',envs') =
          (it (printf "pass: %s -> %s#" (showProg p) (showProg p'))
           ((nsts (p,n,e,envs) `shouldBe` (p',n',e',envs'))
             >> (isNstIrreducible (p',n',e',envs') `shouldBe` True)))

        nstsItFail err (p,n,e,envs) =
          (it (printf "fail: %s ***%s" (showProg p) err)
           (forceEval (nsts (p,n,e,envs)) `shouldThrow` errorCall err))

        reactionItPass (p,e,envs) (p',envs') =
          (it (printf "pass: %d | %s -> %s" e (showProg p) (showProg p'))
            (reaction (p,e,envs) `shouldBe` (p',envs')))

        evalProgItPass res hist prog =
          (it (printf "pass: %s | %s ~>%d" (show hist) (showProg prog) res) $
            (evalProg prog hist `shouldBe` res))

        evalProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (showProg prog) err) $
            (forceEval (evalProg prog hist) `shouldThrow` errorCall err))
