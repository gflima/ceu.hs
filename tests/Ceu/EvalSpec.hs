module Ceu.EvalSpec (main, spec) where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Exp, Stmt, and Desc as datatypes that can be fully evaluated.
instance NFData Exp where
  rnf (Const _)   = ()
  rnf (Read _)    = ()
  rnf (Umn e)     = rnf e
  rnf (Add e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Sub e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Mul e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Div e1 e2) = rnf e1 `deepseq` rnf e2

instance NFData Stmt where
  rnf (Write var expr) = rnf expr
  rnf (AwaitExt _)     = ()
  rnf (AwaitInt _)     = ()
  rnf (EmitInt _)      = ()
  rnf (Break)          = ()
  rnf (If expr p q)    = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq p q)        = rnf p `deepseq` rnf q
  rnf (Every _ p)      = rnf p
  rnf (And p q)        = rnf p `deepseq` rnf q
  rnf (Or p q)         = rnf p `deepseq` rnf q
  rnf (Fin p)          = rnf p
  rnf (Nop)            = ()
  rnf (Error _)        = ()
  rnf (CanRun _)       = ()
  rnf (Var' _ _ p)     = rnf p
  rnf (Int _ p)        = rnf p
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
  describe "Env/Envs" $ do

      it "fail: undeclared variable" $
        forceEval (varsWrite [] "x" 0)
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "pass: 1st write" $
        varsWrite [("x",Nothing)] "x" 0 `shouldBe` [("x",Just 0)]

      it "pass: 2nd write" $
        varsWrite [("x",Just 99)] "x" 0 `shouldBe` [("x",Just 0)]

      it "pass: write in middle" $
        varsWrite [("a",Nothing),("x",Just 99),("b",Nothing)] "x" 0 `shouldBe` [("a",Nothing),("x",Just 0),("b",Nothing)]

      it "pass: write in last" $
        varsWrite [("a",Nothing),("b",Nothing),("x",Just 99)] "x" 0 `shouldBe` [("a",Nothing),("b",Nothing),("x",Just 0)]

  describe "varsRead vars id" $ do
      it "fail: undeclared variable" $
        forceEval (varsRead [] "x")
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsRead [("x",Nothing)] "x")
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: read in simple env" $
        varsRead [("x",Just 0)] "x" `shouldBe` 0

      it "pass: read in complex env" $
        let vars = [("y",Just 0),("x",Just 1),("z",Just 0)] in
          varsRead vars "x" `shouldBe` 1

  describe "varsEval vars exp" $ do
      it "pass: vars == [] && exp == (Const _)" $
        varsEval [] (Const 0) `shouldBe` 0

      it "fail: undeclared variable" $
        forceEval (varsEval [] (Read "x"))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsEval [("x",Nothing)] (Read "x"))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: eval in simple env" $
        let vars = [("x",Just 1),("y",Just 2)] in
          varsEval vars (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let vars = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval vars (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "step" $ do

    -- error --
    describe "(Error \"erro\")" $ do
      it "fail: error \"erro\"" $
        (forceEval $ step (Error "erro", 0, [], [], []))
        `shouldThrow` errorCall "Runtime error: erro"

{-
    -- var --
    describe "(Var \"x\" p)" $ do
      it "pass: Var \"x\" Nop" $
        step (Var "x" Nop, 0, [], [], [])
        `shouldBe` (Var' "x" Nothing Nop, 0, [], [], [])

      it "pass: Var [\"x\"] p" $
        step (Var "x" (Seq Nop Nop), 0, [], [], [])
        `shouldBe` (Var' "x" Nothing (Seq Nop Nop), 0, [], [], [])
-}

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        (forceEval $ step (Write "x" (Read "y"), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        (forceEval $ step (Write "x" (Const 1), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "pass: [x=?] x=1" $
        step (Var' "x" Nothing (Write "x" (Const 1)), 0, [], [], [])
        `shouldBe` (Var' "x" (Just 1) Nop, 0, [], [], [])

      it "pass: [x=1] x=2" $
        step (Var' "x" (Just 1) (Write "x" (Const 2)), 0, [], [], [])
        `shouldBe` (Var' "x" (Just 2) Nop, 0, [], [], [])

      -- TODO: test is correct but fails
      it "fail: [x=1,y=?] x=y (uninitialized variable) | TODO: ok" $
        let p = Var' "x" (Just 1)
               (Var' "y" Nothing
                 (Write "x" (Read "y"))) in
          (forceEval $ step (p, 0, [], [], []))
          `shouldThrow` errorCall "varsRead: uninitialized variable: y"

      it "pass: nop; x=1" $
        step
        (Var' "x" Nothing
          (Nop `Seq` (Write "x" (Const 1))), 0, [], [], [])
        `shouldBe`
        (Var' "x" Nothing
          (Write "x" (Const 1)), 0, [], [], [])

      it "pass: [x=1,y=?] y=x+2" $
        step (
          (Var' "x" (Just 1)
          (Var' "y" Nothing
            (Write "y" (Read "x" `Add` Const 2))), 0, [], [], []))
        `shouldBe` (Var' "x" (Just 1) (Var' "y" (Just 3) Nop),0,[],[], [])

      it "pass: [x=1,y=?] y=x+2" $
        step
        (Var' "x" (Just 1)
        (Var' "y" Nothing
          (Write "y" (Read "x" `Add` Const 2))), 0, [], [], [])
        `shouldBe`
        (Var' "x" (Just 1)
        (Var' "y" (Just 3) Nop), 0, [], [], [])

      it "pass: [x=?] x=-(5+1)" $
        step
        (Var' "x" (Just 0)
          (Write "x" (Umn (Const 5 `Add` Const 1))), 0, [], [], [])
        `shouldBe`
        (Var' "x" (Just (-6)) Nop, 0, [], [], [])

    -- emit-int --
  describe "(EmitInt e')" $ do
      it "fail: {? emit a}" $
        forceEval (step (EmitInt "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: lvl == 0" $
        step (Int "a" (EmitInt "a"), 0, [], [], [])
        `shouldBe` (Int "a" (CanRun 0), 1, [], [], [])

      it "pass: pop" $
        (step (Int "a" (CanRun 0), 1, [], [], []))
        `shouldBe` (Int "a" (CanRun 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int "b" (EmitInt "b"), 3, [], [], [])
        `shouldBe` (Int "b" (CanRun 3), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (EmitInt "b", 3, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- can-run --
  describe "(CanRun n)" $ do
      it "pass: n == lvl" $
        step (CanRun 0, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "pass: n == lvl" $
        step (CanRun 8, 8, [], [], [])
        `shouldBe` (Nop, 8, [], [], [])

      it "pass: n > lvl (pop)" $
        (step (CanRun 8, 6, [], [], []))
        `shouldBe` (CanRun 8, 5, [], [], [])

      it "pass: n < lvl (pop)" $
        step (CanRun 8, 12, [], [], [])
        `shouldBe` (CanRun 8, 11, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (CanRun 0, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-nop --
  describe "(Seq Nop q)" $ do
      it "pass: lvl == 0" $
        step (Seq Nop Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq Nop Break, 3, [], [], [])
        `shouldBe` (Break, 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-brk --
  describe "(Seq Break q)" $ do
      it "pass: lvl == 0" $
        step (Seq Break Nop, 0, [], [], [])
        `shouldBe` (Break, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq Break (EmitInt "z"), 3, [], [], [])
        `shouldBe` (Break, 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq Break Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-adv --
  describe "(Seq p q)" $ do
      it "pass: lvl == 0" $
        step (Seq (Seq Nop Nop) Nop, 0, [], [], [])
        `shouldBe` (Seq Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq (Seq (Int "z" (EmitInt "z")) Nop) Nop, 3, [], [], [])
        `shouldBe` (Seq (Seq (Int "z" (CanRun 3)) Nop) Nop, 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq (Seq Nop Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "fail: isBlocked p (cannot advance)" $
        forceEval (step (Seq (Fin Nop) Nop, 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- if-true/false --
  describe "(If exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (step (If (Read "x") Nop Break, 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "pass: x == 0" $
        step (If (Read "x") Nop Break, 0, [("x",Just 0)], [], [])
        `shouldBe` (Break, 0, [("x",Just 0)], [], [])

      it "pass: x /= 0" $
        step (If (Read "x") Nop Break, 0, [("x",Just 1)], [], [])
        `shouldBe` (Nop, 0, [("x",Just 1)], [], [])

{-
  -- loop-expd --
  describe "(Loop p)" $ do
      it "pass: lvl == 0" $
        step (Loop Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop (Seq Nop (EmitInt "z")), 3, [], [], [])
        `shouldBe`
        (Loop' (Seq Nop (EmitInt "z")) (Seq Nop (EmitInt "z")), 3, [], [], [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        step (Loop (Fin Nop), 0, [], [], [])
        `shouldBe` (Loop' (Fin Nop) (Fin Nop),
                     0, [], [], [])
-}

  -- loop-nop --
  describe "(Loop' Nop q)" $ do
      it "pass: lvl == 0" $
        step (Loop' Nop Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' Nop (EmitInt "z"), 3, [], [], [])
        `shouldBe` (Loop' (EmitInt "z") (EmitInt "z"), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Loop' (Fin Nop) (Fin Nop), 0, [], [], [])

  -- loop-brk --
  describe "(Loop' Break q)" $ do
      it "pass: lvl == 0" $
        step (Loop' Break Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' Break (Seq (EmitInt "z") Nop), 3, [], [], [])
        `shouldBe` (Nop, 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' Break Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' Break (Fin Nop), 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

  -- loop-adv --
  describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Seq Nop Nop) Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int "z" (Loop' (Seq (EmitInt "z") Nop) Break), 3, [], [], [])
        `shouldBe` (Int "z" (Loop' (Seq (CanRun 3) Nop) Break), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' (Seq Nop Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "fail: isBlocked p (cannot advance)" $
        forceEval (step (Loop' (Fin Nop) Nop, 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Loop' (Seq Nop Nop) (Fin Nop), 0, [], [], [])
        `shouldBe` (Loop' Nop (Fin Nop), 0, [], [], [])

  -- and-expd --
  describe "(And p q)" $ do
      it "pass: lvl == 0" $
        step (And Nop Nop, 0, [], [], [])
        `shouldBe` (And' Nop (Seq (CanRun 0) Nop), 0, [], [], [])

      it "pass: lvl > 0" $
        step (And (Nop `Seq` EmitInt "z")  (Nop `Seq` Nop),
               3, [], [], [])
        `shouldBe` (And' (Nop `Seq` EmitInt "z")
                     (CanRun 3 `Seq` Nop `Seq` Nop), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (And (Fin Nop) Nop, 0, [], [], [])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (And Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (And' Nop (Seq (CanRun 0) (Fin Nop)),
                     0, [], [], [])

      it "pass: isBlocked p && isBlocked q" $
        step (And (Fin Nop) (Fin Nop), 0, [], [], [])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
                     0, [], [], [])

  -- and-nop1 --
  describe "(And' Nop q)" $ do
      it "pass: lvl == 0" $
        step (And' Nop Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (And' Nop (EmitInt "z"), 3, [], [], [])
        `shouldBe` (EmitInt "z", 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (And' Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Fin Nop, 0, [], [], [])

      it "pass: q == Nop" $
        step (And' Nop Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "pass: q == Break" $
        step (And' Nop Break, 0, [], [], [])
        `shouldBe` (Break, 0, [], [], [])

  -- and-brk1 --
  describe "(And' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitExt "A") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (And' Break q, 0, [], [], [])
            `shouldBe` (Seq (clear q) Break, 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (And' Break q, 3, [], [], [])
           `shouldBe` (Seq (clear q) Break, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And' Break (Var' "_" Nothing Nop), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (step (And' Break q, 0, [], [], [])
            `shouldBe` (Seq (clear q) Break, 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (And' Break q, 0, [], [], [])
            `shouldBe` (Seq (clear q) Break, 0, [], [], []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (step (And' Break Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (step (And' Break Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-nop2 --
  describe "(And' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        step (And' (Fin Nop) Nop, 0, [], [], [])
        `shouldBe` (Fin Nop, 0, [], [], [])

      it "pass: lvl > 0 && isBlocked p" $
        step (And' (Seq (Fin Nop) Nop) Nop, 3, [], [], [])
        `shouldBe` (Seq (Fin Nop) Nop, 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And' (Fin Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: p == Nop" $
        step (And' Nop Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

      it "fail: p == Break (invalid clear)" $
        forceEval (step (And' Break Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-brk2 --
  describe "(And' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (And' p Break, 0, [], [], [])
           `shouldBe` (Seq (clear p) Break, 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` (Seq Nop Nop))
          >>
          (step (And' p Break, 3, [], [], [])
           `shouldBe` (Seq (clear p) Break, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And' (Fin Nop) Break, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_p = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (step (And' p Break, 0, [], [], [])
            `shouldBe` (Seq (clear p) Break, 0, [], [], []))

      it "pass: p == Nop" $
        step (And' Nop Break, 0, [], [], [])
        `shouldBe` (Break, 0, [], [], [])

      it "fail: p == Break (invalid clear)" $
        forceEval (step (And' Break Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-adv --
  describe "(And' p q)" $ do
      it "pass: lvl == 0" $
        step (And' (Seq Nop Nop) (Seq Break Break), 0, [], [], [])
        `shouldBe` (And' Nop (Seq Break Break), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int "y" (Int "z" (And' (Seq (EmitInt "z") Nop) (Seq (EmitInt "y") Nop))),
               3, [], [], [])
        `shouldBe` (Int "y" (Int "z" (And' (Seq (CanRun 3) Nop) (Seq (EmitInt "y") Nop))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And' (Seq Nop Nop) (Seq Nop Nop),
                         0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (And' (Fin Nop) (Seq (Int "z" (EmitInt "z")) Nop),
               3, [], [], [])
        `shouldBe` (And' (Fin Nop) (Seq (Int "z" (CanRun 3)) Nop),
                     4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Int "z" (And' (EmitInt "z") (AwaitInt "z")), 3, [], [], [])
        `shouldBe` (Int "z" (And' (CanRun 3) Nop), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (And' (AwaitInt "d") (AwaitInt "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- or-expd --
  describe "(Or p q)" $ do
      it "pass: lvl == 0" $
        step (Or Nop Nop, 0, [], [], [])
        `shouldBe` (Or' Nop (Seq (CanRun 0) Nop),
                     0, [], [], [])

      it "pass: lvl > 0" $
        step (Or (Seq Nop (EmitInt "z")) (Seq Nop Nop), 3, [], [], [])
        `shouldBe` (Or' (Seq Nop (EmitInt "z"))
                          (Seq (CanRun 3) (Seq Nop Nop)),
                     3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Or (Fin Nop) Nop, 0, [], [], [])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Or Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Or' Nop (Seq (CanRun 0) (Fin Nop)),
                     0, [], [], [])

      it "pass: isBlocked p && isBlocked q" $
        step (Or (Fin Nop) (Fin Nop), 0, [], [], [])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)), 0, [], [], [])

  -- or-nop1 --
  describe "(Or' Nop q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Or' Nop q, 0, [], [], [])
           `shouldBe` (clear q, 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Or' Nop q, 3, [], [], [])
           `shouldBe` (clear q, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = (Fin Nop) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Or' Nop q, 0, [], [], [])
           `shouldBe` (clear q, 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Or' Nop q, 0, [], [], [])
            `shouldBe` (clear q, 0, [], [], []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (step (Or' Nop Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (step (Or' Nop Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-brk1 --
  describe "(Or' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Or' Break q, 0, [], [], [])
           `shouldBe` (Seq (clear q) Break, 0, [], [], []))

      it "transit: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q`shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Or' Break q, 3, [], [], [])
           `shouldBe` (Seq (clear q) Break, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' Break Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (step (Or' Break q, 0, [], [], [])
           `shouldBe` (Seq (clear q) Break, 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Or' Break q, 0, [], [], [])
            `shouldBe` (Seq clear_q Break, 0, [], [], []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (step (Or' Break Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (step (Or' Break Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-nop2 --
  describe "(Or' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin Nop) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Or' p Nop, 0, [], [], [])
            `shouldBe` (clear p, 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq (Fin Nop) Nop in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Or' p Nop, 3, [], [], [])
            `shouldBe` (clear p, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' (Fin Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "fail: p == Nop (invalid clear)" $
        forceEval (step (Or' Nop Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (step (Or' Break Nop, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-brk2 --
  describe "(Or' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Or' p Break, 0, [], [], [])
           `shouldBe` (Seq (clear p) Break, 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` Seq Nop Nop)
          >>                    -- clear p == Nop; Nop
          (step (Or' p Break, 3, [], [], [])
            `shouldBe` (Seq (clear p) Break, 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' (Fin Nop) Break, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_p = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Or' p Break, 0, [], [], [])
            `shouldBe` (Seq (clear p) Break, 0, [], [], []))

      it "fail: p == Nop (invalid clear)" $
        forceEval (step (Or' Nop Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (step (Or' Break Break, 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-adv --
  describe "(Or' p q)" $ do
      it "pass: lvl == 0" $
        step (Or' (Seq Nop Nop) (Seq Break Break), 0, [], [], [])
        `shouldBe` (Or' Nop (Seq Break Break), 0, [], [], [])

      it "psas: lvl > 0" $
        step (Or' (Int "z" (Seq (EmitInt "z") Nop)) (Int "y" (Seq (EmitInt "y") Nop)),
               3, [], [], [])
        `shouldBe` (Or' (Int "z" (Seq (CanRun 3) Nop)) (Int "y" (Seq (EmitInt "y") Nop)),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' (Seq Nop Nop) (Seq Nop Nop),
                          0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Or' (Fin Nop) (Int "z" (Seq (EmitInt "z") Nop)), 3, [], [], [])
        `shouldBe` (Or' (Fin Nop) (Int "z" (Seq (CanRun 3) Nop)), 4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Int "z" (Or' (EmitInt "z") (AwaitInt "z")), 3, [], [], [])
        `shouldBe` (Int "z" (Or' (CanRun 3) Nop), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Or' (AwaitInt "d") (AwaitInt "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (program is blocked)" $ do

      stepsItPass
        (AwaitExt "A", 0, [], [], [])
        (AwaitExt "A", 0, [], [], [])

      stepsItPass
        (AwaitInt "a", 0, [], [], [])
        (AwaitInt "a", 0, [], [], [])

      stepsItPass
        (Seq (AwaitInt "a") Nop, 0, [], [], [])
        (Seq (AwaitInt "a") Nop, 0, [], [], [])

      stepsItPass
        (Every "A" Nop, 0, [], [], [])
        (Every "A" Nop, 0, [], [], [])

      stepsItPass
        (Fin (Seq Nop Nop), 0, [], [], [])
        (Fin (Seq Nop Nop), 0, [], [], [])

      stepsItPass
        (And' (AwaitExt "A") (Fin Nop), 0, [], [], [])
        (And' (AwaitExt "A") (Fin Nop), 0, [], [], [])

      stepsItPass
        (Or' (AwaitExt "A") (Fin Nop), 0, [], [], [])
        (Or' (AwaitExt "A") (Fin Nop), 0, [], [], [])

{-
      stepsItFail "step: cannot advance"
        (CanRun 5, 0, [], [], [])
-}

    describe "zero steps (no step-rule applies)" $ do

      stepsItPass
        (Nop, 0, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Break, 0, [], [], [])
        (Break, 0, [], [], [])

    describe "one+ steps" $ do

      stepsItPass
        (Var' "x" Nothing (Write "x" (Const 0)), 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Int "z" (EmitInt "z"), 3, [], [], [])
        (Nop, 0, [], [], [])
        --(Int "z" (CanRun 3), 4, [], [], [])

      stepsItPass
        (CanRun 3, 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop, 0, [], [], [])
        (Break, 0, [], [], [])

      stepsItPass
        (Loop' Break Break `Seq` Nop `Seq` Nop `Seq` (Int "z" (EmitInt "z")) `Seq` Break,
          3, [], [], [])
        (Break, 0, [], [], [])

      stepsItPass
        (Seq (Loop' Break Break) Nop `And` Seq (Int "z" (EmitInt "z")) Nop, 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Seq (Loop' Break Break) Nop `Or` Seq (Int "z" (EmitInt "z")) Nop, 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Loop'
          ((Nop `Seq` AwaitInt "d") `And`
            (AwaitExt "M" `Or` (Nop `Seq` Break)))
          ((Nop `Seq` AwaitInt "d") `And`
            (AwaitExt "M" `Or` (Nop `Seq` Break))), 0, [], [], [])
        (Nop, 0, [], [], [])

  --------------------------------------------------------------------------
  describe "out1" $ do

{-
    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 (Nop, 0, Just "b", [], [])
        `shouldBe` (Nop, 1, [], [], [])

      it "pass: lvl > 0" $
        out1 (Seq (AwaitInt "b") Break, 3, Just "b", [], [])
        `shouldBe` (Seq Nop Break, 4, [], [], [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt "c") Break, 3, Just "b", [], [])
        `shouldBe` (Seq (AwaitInt "c") Break, 4, [], [], [])

    -- pop --
    describe "pop" $ do
      it "fail: lvl == 0 (cannot advance)" $
        forceEval (out1 (Nop, 0, [], [], []))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "pass: lvl > 0 && not (isReducible p)" $
        out1 (Nop, 33, [], [], [])
        `shouldBe` (Nop, 32, [], [], [])

      it "pass: lvl > 0 && not (nstReducible p)" $
        forceEval (out1 (Seq Nop Nop, 1, [], [], []))
        `shouldThrow` errorCall "outPop: cannot advance"
-}

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (no out-rule applies)" $ do
      it "pass: lvl == 0 && not (isReducible p)" $
        let d = (Nop, 0, [], [], []) in
          (steps d `shouldBe` d)
          >> ((isReducible d) `shouldBe` False)
          -- >> (isReducible d `shouldBe` True)

      it "pass: lvl == 0 && not (not (isReducible p))" $
        let d = (Seq Nop Nop, 0, [], [], []) in
          (steps d `shouldBe` (Nop,0,[],[], []))
          >> ((isReducible d) `shouldBe` True)
          -- >> (isReducible d `shouldBe` False)

    describe "one+ pops" $ do
      it "pass: lvl > 0" $
        let d = (Int "x" (EmitInt "x"), 0, [], [], [])
            d' = (Nop, 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl>0, but `Nop`" $
        let d = (Nop, 13, [], [], []) in
          (steps d `shouldBe` (Nop, 0, [], [], []))
          >> (isReducible d `shouldBe` True)

    describe "one push followed by one+ pops" $ do
      it "pass: lvl == 0 (do nothing)" $ -- CHECK THIS! --
        let d = (bcast "c" (AwaitInt "d"), 0, [], [], [])
            d' = (AwaitInt "d", 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl > 0, but `Nop`" $
        let d = (bcast "d" (AwaitInt "d"), 88, [], [], [])
            d' = (Nop, 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      (Int "d"
        (And
          (EmitInt "d")
          ((Nop `Seq` AwaitInt "d") `And` (Nop `Seq` Fin Nop)
      )), "_", [])
      (Int "d" (AwaitInt "d" `And'` Fin Nop), [], [])

    reactionItPass
      (Int "d" ((Nop `Seq` AwaitInt "d") `And` (Nop `Seq` EmitInt "d")), "_", [])
      (Nop, [], [])

  --------------------------------------------------------------------------
  describe "evalProg" $ do

    evalProgItPass (11,[[]])
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItFail "evalProg: no return"
      [] (G.Var "a"
           (G.Var "ret"
             (G.Write "a" (Const 1) `G.Seq`
              G.Write "ret" (Read "a" `Add` Const 10))))

    evalProgItPass (1,[[]])
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Var "ret" (G.Write "ret" (Const 99)))

    evalProgItPass (11,[[]])
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Var "a" (G.Write "a" (Const 99)) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass (2,[[]])
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Var "_" (G.Write "ret" (Const 2)))

    evalProgItPass (11,[[]])
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Or
             (G.Var "a" (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
             (G.Nop) `G.Seq`
           G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass (1,[[]])
      [] (G.Or
           (G.Var "x" (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
           (G.Nop))

    evalProgItPass (11,[[]])
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Loop (G.And
                  (G.Var "a" (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
                  (G.Break)) `G.Seq`
             G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass (1,[[]])
      [] (G.Loop (G.And
                 (G.Var "x" (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
                 (G.Break)))

    evalProgItPass (5,[[]]) [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.Int "a"
        (G.And
          ((G.AwaitInt "a") `G.Seq` (G.Write "ret" (Const 5)))
          (G.EmitInt "a")
      )))

    evalProgItPass (5,[[]]) [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.Int "a"
        (G.Or
          ((G.AwaitInt "a") `G.Seq` (G.Write "ret" (Const 5)))
          (G.Or (G.Fin (G.EmitInt "a")) G.Nop)
      )))

{-
var x;
x = 10;
par/or do
    var x;
    await FOREVER;
with
    x = 99;
end
escape x;
-}
    evalProgItPass (99,[[]]) [] (
      (G.Var "x" (
        (G.Write "x" (Const 10)) `G.Seq`
        (G.Or
          (G.Var "x" (G.AwaitExt "FOREVER"))
          (G.Write "x" (Const 99))
        ) `G.Seq`
        (G.Write "ret" (Read "x"))
      )))

    -- multiple inputs

    evalProgItPass (1,[[],[]])
      ["A"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      [] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: program didn't terminate"
      ["B"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItFail "evalProg: pending inputs"
      ["A","A"] (G.AwaitExt "A" `G.Seq` G.Write "ret" (Const 1))

    evalProgItPass (1,[[],[],[]])
      ["A","B"] (G.AwaitExt "A" `G.Seq` G.AwaitExt "B" `G.Seq` G.Write "ret" (Const 1))

    evalProgItPass (1,[[]]) [] (G.Write "ret" (Const 1))

    evalProgItFail "evtsEmit: undeclared event: a" [] (
      (G.Write "ret" (Const 25)) `G.Seq`
      (G.EmitInt "a")
      )

    -- multiple outputs

    evalProgItPass (1,[[],[("O",Nothing)],[("O",Nothing)],[]]) ["I","I","F"]
      (G.Seq (G.Write "ret" (Const 1))
        (G.Or (G.AwaitExt "F") (G.Every "I" (G.EmitExt "O" Nothing))))

      where
        stepsItPass (p,n,e,vars,outs) (p',n',e',vars',outs') =
          (it (printf "pass: %s -> %s#" (showProg p) (showProg p'))
           ((steps (p,n,e,vars,outs) `shouldBe` (p',n',e',vars',outs'))
             >> ((isReducible (p',n',e',vars',outs')) `shouldBe` False)))

        stepsItFail err (p,n,e,vars,outs) =
          (it (printf "fail: %s ***%s" (showProg p) err)
           (forceEval (steps (p,n,e,vars,outs)) `shouldThrow` errorCall err))

        reactionItPass (p,e,vars) (p',vars',outs') =
          (it (printf "pass: %s | %s -> %s" e (showProg p) (showProg p'))
            (reaction p e `shouldBe` (p',outs')))

        --evalProgItPass :: (Val,[Outs]) -> [ID_Ext] -> Stmt -> IO a
        evalProgItPass (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg prog) res (show outss)) $
            (evalProg prog hist `shouldBe` (res,outss)))

        evalProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg prog) err) $
            (forceEval (evalProg prog hist) `shouldThrow` errorCall err))
