module Ceu.EvalSpec (main, spec) where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Ceu.Eval
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

  describe "envsRead envs id" $ do
      it "fail: undeclared variable" $
        forceEval (varsRead [] "x")
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsRead [("x",Nothing)] "x")
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: read in simple env" $
        varsRead [("x",Just 0)] "x" `shouldBe` 0

      it "pass: read in complex env" $
        let envs = [("y",Just 0),("x",Just 1),("z",Just 0)] in
          varsRead envs "x" `shouldBe` 1

  describe "varsEval envs exp" $ do
      it "pass: envs == [] && exp == (Const _)" $
        varsEval [] (Const 0) `shouldBe` 0

      it "fail: undeclared variable" $
        forceEval (varsEval [] (Read "x"))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsEval [("x",Nothing)] (Read "x"))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: eval in simple env" $
        let envs = [("x",Just 1),("y",Just 2)] in
          varsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let envs = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval envs (((Read "x") `Sub` Const 3) `Add` Umn (Read "y"))
          `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "nst1" $ do

    -- error --
    describe "(Error \"erro\")" $ do
      it "fail: error \"erro\"" $
        (forceEval $ nst1 (Error "erro", 0, Nothing, []))
        `shouldThrow` errorCall "Runtime error: erro"

{-
    -- var --
    describe "(Var \"x\" p)" $ do
      it "pass: Var \"x\" Nop" $
        nst1 (Var "x" Nop, 0, Nothing, [])
        `shouldBe` (Var' "x" Nothing Nop, 0, Nothing, [])

      it "pass: Var [\"x\"] p" $
        nst1 (Var "x" (Seq Nop Nop), 0, Nothing, [])
        `shouldBe` (Var' "x" Nothing (Seq Nop Nop), 0, Nothing, [])
-}

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        (forceEval $ nst1 (Write "x" (Read "y"), 0, Nothing, []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        (forceEval $ nst1 (Write "x" (Const 1), 0, Nothing, []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "pass: [x=?] x=1" $
        nst1 (Var' "x" Nothing (Write "x" (Const 1)), 0, Nothing, [])
        `shouldBe` (Var' "x" (Just 1) Nop, 0, Nothing, [])

      it "pass: [x=1] x=2" $
        nst1 (Var' "x" (Just 1) (Write "x" (Const 2)), 0, Nothing, [])
        `shouldBe` (Var' "x" (Just 2) Nop, 0, Nothing, [])

      -- TODO: test is correct but fails
      it "fail: [x=1,y=?] x=y (uninitialized variable) | TODO: ok" $
        let p = Var' "x" (Just 1)
               (Var' "y" Nothing
                 (Write "x" (Read "y"))) in
          (forceEval $ nst1 (p, 0, Nothing, []))
          `shouldThrow` errorCall "varsRead: uninitialized variable: y"

      it "pass: nop; x=1" $
        nst1
        (Var' "x" Nothing
          (Nop `Seq` (Write "x" (Const 1))), 0, Nothing, [])
        `shouldBe`
        (Var' "x" Nothing
          (Write "x" (Const 1)), 0, Nothing, [])

      it "pass: [x=1,y=?] y=x+2" $
        nst1 (
          (Var' "x" (Just 1)
          (Var' "y" Nothing
            (Write "y" (Read "x" `Add` Const 2))), 0, Nothing, []))
        `shouldBe` (Var' "x" (Just 1) (Var' "y" (Just 3) Nop),0,Nothing,[])

      it "pass: [x=1,y=?] y=x+2" $
        nst1
        (Var' "x" (Just 1)
        (Var' "y" Nothing
          (Write "y" (Read "x" `Add` Const 2))), 0, Nothing, [])
        `shouldBe`
        (Var' "x" (Just 1)
        (Var' "y" (Just 3) Nop), 0, Nothing, [])

      it "pass: [x=?] x=-(5+1)" $
        nst1
        (Var' "x" (Just 0)
          (Write "x" (Umn (Const 5 `Add` Const 1))), 0, Nothing, [])
        `shouldBe`
        (Var' "x" (Just (-6)) Nop, 0, Nothing, [])

    -- emit-int --
  describe "(EmitInt e')" $ do
      it "pass: lvl == 0" $
        nst1 (EmitInt "a", 0, Nothing, [])
        `shouldBe` (CanRun 0, 0, Just "a", [])

      it "pass: lvl > 0" $
        nst1 (EmitInt "b", 3, Nothing, [])
        `shouldBe` (CanRun 3, 3, Just "b", [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (EmitInt "b", 3, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- can-run --
  describe "(CanRun n)" $ do
      it "pass: n == lvl" $
        nst1 (CanRun 0, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "pass: n == lvl" $
        nst1 (CanRun 8, 8, Nothing, [])
        `shouldBe` (Nop, 8, Nothing, [])

      it "fail: n > lvl (cannot advance)" $
        forceEval (nst1 (CanRun 8, 6, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: n < lvl (cannot advance)" $
        forceEval (nst1 (CanRun 8, 12, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (CanRun 0, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- seq-nop --
  describe "(Seq Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq Nop Nop, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Seq Nop Break, 3, Nothing, [])
        `shouldBe` (Break, 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- seq-brk --
  describe "(Seq Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq Break Nop, 0, Nothing, [])
        `shouldBe` (Break, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Seq Break (EmitInt "z"), 3, Nothing, [])
        `shouldBe` (Break, 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq Break Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- seq-adv --
  describe "(Seq p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Seq (Seq Nop Nop) Nop, 0, Nothing, [])
        `shouldBe` (Seq Nop Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Seq (Seq (EmitInt "z") Nop) Nop, 3, Nothing, [])
        `shouldBe` (Seq (Seq (CanRun 3) Nop) Nop, 3, Just "z", [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Seq (Seq Nop Nop) Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Seq (Fin Nop) Nop, 0, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- if-true/false --
  describe "(If exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (nst1 (If (Read "x") Nop Break, 0, Nothing, []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "pass: x == 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [("x",Just 0)])
        `shouldBe` (Break, 0, Nothing, [("x",Just 0)])

      it "pass: x /= 0" $
        nst1 (If (Read "x") Nop Break, 0, Nothing, [("x",Just 1)])
        `shouldBe` (Nop, 0, Nothing, [("x",Just 1)])

{-
  -- loop-expd --
  describe "(Loop p)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop Nop, 0, Nothing, [])
        `shouldBe` (Loop' Nop Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Loop (Seq Nop (EmitInt "z")), 3, Nothing, [])
        `shouldBe`
        (Loop' (Seq Nop (EmitInt "z")) (Seq Nop (EmitInt "z")), 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        nst1 (Loop (Fin Nop), 0, Nothing, [])
        `shouldBe` (Loop' (Fin Nop) (Fin Nop),
                     0, Nothing, [])
-}

  -- loop-nop --
  describe "(Loop' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' Nop Nop, 0, Nothing, [])
        `shouldBe` (Loop' Nop Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Loop' Nop (EmitInt "z"), 3, Nothing, [])
        `shouldBe` (Loop' (EmitInt "z") (EmitInt "z"), 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' Nop (Fin Nop), 0, Nothing, [])
        `shouldBe` (Loop' (Fin Nop) (Fin Nop), 0, Nothing, [])

  -- loop-brk --
  describe "(Loop' Break q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' Break Nop, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Loop' Break (Seq (EmitInt "z") Nop), 3, Nothing, [])
        `shouldBe` (Nop, 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' Break Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (Loop' Break (Fin Nop), 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

  -- loop-adv --
  describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Loop' (Seq Nop Nop) Nop, 0, Nothing, [])
        `shouldBe` (Loop' Nop Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Loop' (Seq (EmitInt "z") Nop) Break, 3, Nothing, [])
        `shouldBe` (Loop' (Seq (CanRun 3) Nop) Break, 3, Just "z", [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Loop' (Seq Nop Nop) Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        forceEval (nst1 (Loop' (Fin Nop) Nop, 0, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Loop' (Seq Nop Nop) (Fin Nop), 0, Nothing, [])
        `shouldBe` (Loop' Nop (Fin Nop), 0, Nothing, [])

  -- and-expd --
  describe "(And p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And Nop Nop, 0, Nothing, [])
        `shouldBe` (And' Nop (Seq (CanRun 0) Nop), 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (And (Nop `Seq` EmitInt "z")  (Nop `Seq` Nop),
               3, Nothing, [])
        `shouldBe` (And' (Nop `Seq` EmitInt "z")
                     (CanRun 3 `Seq` Nop `Seq` Nop), 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And (Fin Nop) Nop, 0, Nothing, [])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, Nothing, [])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And Nop (Fin Nop), 0, Nothing, [])
        `shouldBe` (And' Nop (Seq (CanRun 0) (Fin Nop)),
                     0, Nothing, [])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (And (Fin Nop) (Fin Nop), 0, Nothing, [])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
                     0, Nothing, [])

  -- and-nop1 --
  describe "(And' Nop q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' Nop Nop, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (And' Nop (EmitInt "z"), 3, Nothing, [])
        `shouldBe` (EmitInt "z", 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        nst1 (And' Nop (Fin Nop), 0, Nothing, [])
        `shouldBe` (Fin Nop, 0, Nothing, [])

      it "pass: q == Nop" $
        nst1 (And' Nop Nop, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "pass: q == Break" $
        nst1 (And' Nop Break, 0, Nothing, [])
        `shouldBe` (Break, 0, Nothing, [])

  -- and-brk1 --
  describe "(And' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitExt "A") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' Break q, 0, Nothing, [])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, []))

      it "pass: lvl > 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (And' Break q, 3, Nothing, [])
           `shouldBe` (Seq (clear q) Break, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' Break (Var' "_" Nothing Nop), 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (And' Break q, 0, Nothing, [])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' Break q, 0, Nothing, [])
            `shouldBe` (Seq (clear q) Break, 0, Nothing, []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (And' Break Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (And' Break Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-nop2 --
  describe "(And' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        nst1 (And' (Fin Nop) Nop, 0, Nothing, [])
        `shouldBe` (Fin Nop, 0, Nothing, [])

      it "pass: lvl > 0 && isBlocked p" $
        nst1 (And' (Seq (Fin Nop) Nop) Nop, 3, Nothing, [])
        `shouldBe` (Seq (Fin Nop) Nop, 3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Fin Nop) Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: p == Nop" $
        nst1 (And' Nop Nop, 0, Nothing, [])
        `shouldBe` (Nop, 0, Nothing, [])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' Break Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-brk2 --
  describe "(And' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (And' p Break, 0, Nothing, [])
           `shouldBe` (Seq (clear p) Break, 0, Nothing, []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` (Seq Nop Nop))
          >>
          (nst1 (And' p Break, 3, Nothing, [])
           `shouldBe` (Seq (clear p) Break, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Fin Nop) Break, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_p = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (And' p Break, 0, Nothing, [])
            `shouldBe` (Seq (clear p) Break, 0, Nothing, []))

      it "pass: p == Nop" $
        nst1 (And' Nop Break, 0, Nothing, [])
        `shouldBe` (Break, 0, Nothing, [])

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (And' Break Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- and-adv --
  describe "(And' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (And' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [])
        `shouldBe` (And' Nop (Seq Break Break), 0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (And' (Seq (EmitInt "z") Nop) (Seq (EmitInt "y") Nop),
               3, Nothing, [])
        `shouldBe` (And' (Seq (CanRun 3) Nop) (Seq (EmitInt "y") Nop),
                     3, Just "z", [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (And' (Seq Nop Nop) (Seq Nop Nop),
                         0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (And' (Fin Nop) (Seq (EmitInt "z") Nop),
               3, Nothing, [])
        `shouldBe` (And' (Fin Nop) (Seq (CanRun 3) Nop),
                     3, Just "z", [])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (And' (EmitInt "z") (AwaitInt "z"), 3, Nothing, [])
        `shouldBe` (And' (CanRun 3) (AwaitInt "z"), 3, Just "z", [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (And' (AwaitInt "d") (AwaitInt "e"),
                          0, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

  -- or-expd --
  describe "(Or p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or Nop Nop, 0, Nothing, [])
        `shouldBe` (Or' Nop (Seq (CanRun 0) Nop),
                     0, Nothing, [])

      it "pass: lvl > 0" $
        nst1 (Or (Seq Nop (EmitInt "z")) (Seq Nop Nop), 3, Nothing, [])
        `shouldBe` (Or' (Seq Nop (EmitInt "z"))
                          (Seq (CanRun 3) (Seq Nop Nop)),
                     3, Nothing, [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or (Fin Nop) Nop, 0, Nothing, [])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, Nothing, [])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or Nop (Fin Nop), 0, Nothing, [])
        `shouldBe` (Or' Nop (Seq (CanRun 0) (Fin Nop)),
                     0, Nothing, [])

      it "pass: isBlocked p && isBlocked q" $
        nst1 (Or (Fin Nop) (Fin Nop), 0, Nothing, [])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 0) (Fin Nop)), 0, Nothing, [])

  -- or-nop1 --
  describe "(Or' Nop q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 0, Nothing, [])
           `shouldBe` (clear q, 0, Nothing, []))

      it "pass: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 3, Nothing, [])
           `shouldBe` (clear q, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' Nop Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = (Fin Nop) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Nop q, 0, Nothing, [])
           `shouldBe` (clear q, 0, Nothing, []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' Nop q, 0, Nothing, [])
            `shouldBe` (clear q, 0, Nothing, []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' Nop Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-brk1 --
  describe "(Or' Break q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Break q, 0, Nothing, [])
           `shouldBe` (Seq (clear q) Break, 0, Nothing, []))

      it "transit: lvl > 0" $
        let q = (AwaitInt "z") in
          (clear q`shouldBe` Nop)
          >>                    -- clear q == Nop
          (nst1 (Or' Break q, 3, Nothing, [])
           `shouldBe` (Seq (clear q) Break, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' Break Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (nst1 (Or' Break q, 0, Nothing, [])
           `shouldBe` (Seq (clear q) Break, 0, Nothing, []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_q = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' Break q, 0, Nothing, [])
            `shouldBe` (Seq clear_q Break, 0, Nothing, []))

      it "fail: q == Nop (invalid clear)" $
        forceEval (nst1 (Or' Break Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: q == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-nop2 --
  describe "(Or' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin Nop) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Nop, 0, Nothing, [])
            `shouldBe` (clear p, 0, Nothing, []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq (Fin Nop) Nop in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Nop, 3, Nothing, [])
            `shouldBe` (clear p, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Fin Nop) Nop, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Nop, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-brk2 --
  describe "(Or' p Break)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (nst1 (Or' p Break, 0, Nothing, [])
           `shouldBe` (Seq (clear p) Break, 0, Nothing, []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` Seq Nop Nop)
          >>                    -- clear p == Nop; Nop
          (nst1 (Or' p Break, 3, Nothing, [])
            `shouldBe` (Seq (clear p) Break, 3, Nothing, []))

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Fin Nop) Break, 0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Or' (AwaitExt "A" `Seq` Fin Nop)
                    (And' (Fin (EmitInt "b"))
                          (Or' (Fin (EmitInt "c" `Seq` EmitInt "d"))
                            (AwaitInt "a" `Seq` Fin (EmitInt "e"))))
            clear_p = Nop `Seq` EmitInt "b" `Seq`
                      (EmitInt "c" `Seq` EmitInt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (nst1 (Or' p Break, 0, Nothing, [])
            `shouldBe` (Seq (clear p) Break, 0, Nothing, []))

      it "fail: p == Nop (invalid clear)" $
        forceEval (nst1 (Or' Nop Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

      it "fail: p == Break (invalid clear)" $
        forceEval (nst1 (Or' Break Break, 0, Nothing, []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-adv --
  describe "(Or' p q)" $ do
      it "pass: lvl == 0" $
        nst1 (Or' (Seq Nop Nop) (Seq Break Break), 0, Nothing, [])
        `shouldBe` (Or' Nop (Seq Break Break), 0, Nothing, [])

      it "psas: lvl > 0" $
        nst1 (Or' (Seq (EmitInt "z") Nop) (Seq (EmitInt "y") Nop),
               3, Nothing, [])
        `shouldBe` (Or' (Seq (CanRun 3) Nop) (Seq (EmitInt "y") Nop),
                     3, Just "z", [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (nst1 (Or' (Seq Nop Nop) (Seq Nop Nop),
                          0, Just "b", []))
        `shouldThrow` errorCall "nst1: cannot advance"

      it "pass: isBlocked p && not (isBlocked q)" $
        nst1 (Or' (Fin Nop) (Seq (EmitInt "z") Nop), 3, Nothing, [])
        `shouldBe` (Or' (Fin Nop) (Seq (CanRun 3) Nop), 3, Just "z", [])

      it "pass: not (isBlocked p) && isBlocked q" $
        nst1 (Or' (EmitInt "z") (AwaitInt "z"), 3, Nothing, [])
        `shouldBe` (Or' (CanRun 3) (AwaitInt "z"), 3, Just "z", [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (nst1 (Or' (AwaitInt "d") (AwaitInt "e"),
                          0, Nothing, []))
        `shouldThrow` errorCall "nst1: cannot advance"

  --------------------------------------------------------------------------
  describe "nsts" $ do
    describe "zero steps (program is blocked)" $ do

      nstsItPass
        (AwaitExt "A", 0, Nothing, [])
        (AwaitExt "A", 0, Nothing, [])

      nstsItPass
        (AwaitInt "a", 0, Nothing, [])
        (AwaitInt "a", 0, Nothing, [])

      nstsItPass
        (Seq (AwaitInt "a") Nop, 0, Nothing, [])
        (Seq (AwaitInt "a") Nop, 0, Nothing, [])

      nstsItPass
        (Every "A" Nop, 0, Nothing, [])
        (Every "A" Nop, 0, Nothing, [])

      nstsItPass
        (Fin (Seq Nop Nop), 0, Nothing, [])
        (Fin (Seq Nop Nop), 0, Nothing, [])

      nstsItPass
        (And' (AwaitExt "A") (Fin Nop), 0, Nothing, [])
        (And' (AwaitExt "A") (Fin Nop), 0, Nothing, [])

      nstsItPass
        (Or' (AwaitExt "A") (Fin Nop), 0, Nothing, [])
        (Or' (AwaitExt "A") (Fin Nop), 0, Nothing, [])

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
        (Var' "x" Nothing (Write "x" (Const 0)), 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (EmitInt "z", 3, Nothing, [])
        (CanRun 3, 3, Just "z", [])

      nstsItPass
        (CanRun 3, 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (Nop `Seq` Nop `Seq` Nop `Seq` Break `Seq` Nop, 0, Nothing, [])
        (Break, 0, Nothing, [])

      nstsItPass
        (Loop' Break Break `Seq` Nop `Seq` Nop `Seq` EmitInt "z" `Seq` Break,
          3, Nothing, [])
        (Seq (CanRun 3) Break, 3, Just "z", [])

      nstsItPass
        (Seq (Loop' Break Break) Nop `And` Seq (EmitInt "z") Nop, 3, Nothing, [])
        (Seq (CanRun 3) Nop, 3, Just "z", [])

      nstsItPass
        (Seq (Loop' Break Break) Nop `Or` Seq (EmitInt "z") Nop, 3, Nothing, [])
        (Nop, 3, Nothing, [])

      nstsItPass
        (Loop'
          ((Nop `Seq` AwaitInt "d") `And`
            (AwaitExt "M" `Or` (Nop `Seq` Break)))
          ((Nop `Seq` AwaitInt "d") `And`
            (AwaitExt "M" `Or` (Nop `Seq` Break))), 0, Nothing, [])
        (Nop, 0, Nothing, [])

  --------------------------------------------------------------------------
  describe "out1" $ do

    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 (Nop, 0, Just "b", [])
        `shouldBe` (Nop, 1, Nothing, [])

      it "pass: lvl > 0" $
        out1 (Seq (AwaitInt "b") Break, 3, Just "b", [])
        `shouldBe` (Seq Nop Break, 4, Nothing, [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitInt "c") Break, 3, Just "b", [])
        `shouldBe` (Seq (AwaitInt "c") Break, 4, Nothing, [])

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
        let d = (AwaitInt "d", 0, Just "c", [])
            d' = (AwaitInt "d", 0, Just "c", []) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          -- >> (isIrreducible d' `shouldBe` True)

      it "pass: lvl > 0" $
        let d = (AwaitInt "d", 88, Just "d", [])
            d' = (Nop, 0, Nothing, []) in
          (nsts_out1_s d `shouldBe` d')
          >> (isNstIrreducible d' `shouldBe` True)
          >> (isIrreducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      ((Nop `Seq` AwaitInt "d") `And` (Nop `Seq` Fin Nop), "d", [])
      (AwaitInt "d" `And'` Fin Nop, [])

    reactionItPass
      ((Nop `Seq` AwaitInt "d") `And` (Nop `Seq` EmitInt "d"), "b", [])
      (Nop, [])

  --------------------------------------------------------------------------
  describe "evalProg" $ do

    evalProgItPass 11
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItFail "evalProg: no return"
      [] (G.Var "a"
           (G.Var "ret"
             (G.Write "a" (Const 1) `G.Seq`
              G.Write "ret" (Read "a" `Add` Const 10))))

    evalProgItPass 1
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Var "ret" (G.Write "ret" (Const 99)))

    evalProgItPass 11
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Var "a" (G.Write "a" (Const 99)) `G.Seq`
            G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 2
      [] (G.Write "ret" (Const 1) `G.Seq`
          G.Var "_" (G.Write "ret" (Const 2)))

    evalProgItPass 11
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Or
             (G.Var "a" (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
             (G.Nop) `G.Seq`
           G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (G.Or
           (G.Var "x" (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
           (G.Nop))

    evalProgItPass 11
      [] (G.Var "a"
           (G.Write "a" (Const 1) `G.Seq`
            G.Loop (G.And
                  (G.Var "a" (G.Write "a" (Const 99) `G.Seq` G.AwaitExt "A"))
                  (G.Break)) `G.Seq`
             G.Write "ret" (Read "a" `Add` Const 10)))

    evalProgItPass 1
      [] (G.Loop (G.And
                 (G.Var "x" (G.Write "ret" (Const 1) `G.Seq` G.AwaitExt "A"))
                 (G.Break)))

    evalProgItPass 5 [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.And
        ((G.AwaitInt "a") `G.Seq` (G.Write "ret" (Const 5)))
        (G.EmitInt "a")
      ))

    evalProgItPass 5 [] (
      (G.Write "ret" (Const 1)) `G.Seq`
      (G.Or
        ((G.AwaitInt "a") `G.Seq` (G.Write "ret" (Const 5)))
        (G.Or (G.Fin (G.EmitInt "a")) G.Nop)
      ))

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
    evalProgItPass 99 [] (
      (G.Var "x" (
        (G.Write "x" (Const 10)) `G.Seq`
        (G.Or
          (G.Var "x" (G.AwaitExt "FOREVER"))
          (G.Write "x" (Const 99))
        ) `G.Seq`
        (G.Write "ret" (Read "x"))
      )))

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
