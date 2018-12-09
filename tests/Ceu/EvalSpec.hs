module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals (ToSourceString(..))
import Ceu.Grammar.ToSourceString.Unit
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Exp, Stmt, and Desc as datatypes that can be fully evaluated.
instance NFData (Exp ann) where
  rnf (Const _ _)     = ()
  rnf (Read  _ _)     = ()
  rnf (Umn   _ e)     = rnf e
  rnf (Add   _ e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Sub   _ e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Mul   _ e1 e2) = rnf e1 `deepseq` rnf e2
  rnf (Div   _ e1 e2) = rnf e1 `deepseq` rnf e2

instance NFData (Stmt ann) where
  rnf (Write _ _ expr) = rnf expr
  rnf (AwaitExt _ _)     = ()
  rnf (AwaitInt _ _)     = ()
  rnf (EmitInt _ _)      = ()
  rnf (If _ expr p q)    = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq _ p q)        = rnf p `deepseq` rnf q
  rnf (Every _ _ p)      = rnf p
  rnf (Par _ p q)        = rnf p `deepseq` rnf q
  rnf (Pause _ _ p)      = rnf p
  rnf (Fin _ p)          = rnf p
  rnf (Trap _ p)         = rnf p
  rnf (Escape _ _)       = ()
  rnf (Nop _)            = ()
  rnf (Error _ _)        = ()
  rnf (CanRun _ _)       = ()
  rnf (Var _ _ p)        = rnf p
  rnf (Int _ _ p)        = rnf p
  rnf (Loop' _ p q)      = rnf p
  rnf (Par' _ p q)       = rnf p `deepseq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

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
      it "pass: vars == [] && exp == (Const () _)" $
        varsEval [] (Const () 0) `shouldBe` 0

      it "fail: undeclared variable" $
        forceEval (varsEval [] (Read () "x"))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsEval [("x",Nothing)] (Read () "x"))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: eval in simple env" $
        let vars = [("x",Just 1),("y",Just 2)] in
          varsEval vars (((Read () "x") `eSub` Const () 3) `eAdd` Umn () (Read () "y"))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let vars = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval vars (((Read () "x") `eSub` Const () 3) `eAdd` Umn () (Read () "y"))
          `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "step" $ do

    -- error --
    describe "(Error () \"erro\")" $ do
      it "fail: error \"erro\"" $
        (forceEval $ step (Error () "erro", 0, [], [], []))
        `shouldThrow` errorCall "Runtime error: erro"

{-
    -- var --
    describe "(Var () \"x\" p)" $ do
      it "pass: Var () \"x\" (Nop ())" $
        step (Var () "x" (Nop ()), 0, [], [], [])
        `shouldBe` (Var () ("x",Nothing) (Nop ()), 0, [], [], [])

      it "pass: Var () [\"x\"] p" $
        step (Var () "x" (Seq () (Nop ()) (Nop ())), 0, [], [], [])
        `shouldBe` (Var () ("x",Nothing) (Seq () (Nop ()) (Nop ())), 0, [], [], [])
-}

    -- write --
    describe "(Write () id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        (forceEval $ step (Write () "x" (Read () "y"), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        (forceEval $ step (Write () "x" (Const () 1), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "pass: [x=?] x=1" $
        step (Var () ("x",Nothing) (Write () "x" (Const () 1)), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 1)) (Nop ()), 0, [], [], [])

      it "pass: [x=1] x=2" $
        step (Var () ("x",(Just 1)) (Write () "x" (Const () 2)), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 2)) (Nop ()), 0, [], [], [])

      -- TODO: test is correct but fails
      it "fail: [x=1,y=?] x=y (uninitialized variable) | TODO: ok" $
        let p = Var () ("x",(Just 1))
               (Var () ("y",Nothing)
                 (Write () "x" (Read () "y"))) in
          (forceEval $ step (p, 0, [], [], []))
          `shouldThrow` errorCall "varsRead: uninitialized variable: y"

      it "fail: TODO: ok" $
        (forceEval $ step (EmitInt () "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "fail: TODO: ok" $
        (forceEval $ step (Var () ("_ret",Nothing) ((Write () "_ret" (Const () 25)) `sSeq` (EmitInt () "a")), 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: nop; x=1" $
        step
        (Var () ("x",Nothing)
          ((Nop ()) `sSeq` (Write () "x" (Const () 1))), 0, [], [], [])
        `shouldBe`
        (Var () ("x",Nothing)
          (Write () "x" (Const () 1)), 0, [], [], [])

      it "pass: [x=1,y=?] y=x+2" $
        step (
          (Var () ("x",(Just 1))
          (Var () ("y",Nothing)
            (Write () "y" (Read () "x" `eAdd` Const () 2))), 0, [], [], []))
        `shouldBe` (Var () ("x",(Just 1)) (Var () ("y",(Just 3)) (Nop ())),0,[],[], [])

      it "pass: [x=1,y=?] y=x+2" $
        step
        (Var () ("x",(Just 1))
        (Var () ("y",Nothing)
          (Write () "y" (Read () "x" `eAdd` Const () 2))), 0, [], [], [])
        `shouldBe`
        (Var () ("x",(Just 1))
        (Var () ("y",(Just 3)) (Nop ())), 0, [], [], [])

      it "pass: [x=?] x=-(5+1)" $
        step
        (Var () ("x",(Just 0))
          (Write () "x" (Umn () (Const () 5 `eAdd` Const () 1))), 0, [], [], [])
        `shouldBe`
        (Var () ("x",(Just (-6))) (Nop ()), 0, [], [], [])

    -- emit-int --
  describe "(EmitInt () e')" $ do
      it "fail: {? emit a}" $
        forceEval (step (EmitInt () "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: lvl == 0" $
        step (Int () "a" (EmitInt () "a"), 0, [], [], [])
        `shouldBe` (Int () "a" (CanRun () 0), 1, [], [], [])

      it "pass: pop" $
        (step (Int () "a" (CanRun () 0), 1, [], [], []))
        `shouldBe` (Int () "a" (CanRun () 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int () "b" (EmitInt () "b"), 3, [], [], [])
        `shouldBe` (Int () "b" (CanRun () 3), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (EmitInt () "b", 3, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- can-run --
  describe "(CanRun () n)" $ do
      it "pass: n == lvl" $
        step (CanRun () 0, 0, [], [], [])
        `shouldBe` ((Nop ()), 0, [], [], [])

      it "pass: n == lvl" $
        step (CanRun () 8, 8, [], [], [])
        `shouldBe` ((Nop ()), 8, [], [], [])

      it "pass: n > lvl (pop)" $
        (step (CanRun () 8, 6, [], [], []))
        `shouldBe` (CanRun () 8, 5, [], [], [])

      it "pass: n < lvl (pop)" $
        step (CanRun () 8, 12, [], [], [])
        `shouldBe` (CanRun () 8, 11, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (CanRun () 0, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-nop --
  describe "(Seq () (Nop ()) q)" $ do
      it "pass: lvl == 0" $
        step (Seq () (Nop ()) (Nop ()), 0, [], [], [])
        `shouldBe` ((Nop ()), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq () (Nop ()) (Escape () 0), 3, [], [], [])
        `shouldBe` ((Escape () 0), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq () (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-brk --
  describe "(Seq () (Escape () k) q)" $ do
      it "pass: lvl == 0" $
        step (Seq () (Escape () 0) (Nop ()), 0, [], [], [])
        `shouldBe` ((Escape () 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq () (Escape () 0) (EmitInt () "z"), 3, [], [], [])
        `shouldBe` ((Escape () 0), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq () Break (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-adv --
  describe "(Seq () p q)" $ do
      it "pass: lvl == 0" $
        step (Seq () (Seq () (Nop ()) (Nop ())) (Nop ()), 0, [], [], [])
        `shouldBe` (Seq () (Nop ()) (Nop ()), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq () (Seq () (Int () "z" (EmitInt () "z")) (Nop ())) (Nop ()), 3, [], [], [])
        `shouldBe` (Seq () (Seq () (Int () "z" (CanRun () 3)) (Nop ())) (Nop ()), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq () (Seq () (Nop ()) (Nop ())) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "fail: isBlocked p (cannot advance)" $
        forceEval (step (Seq () (Fin () (Nop ())) (Nop ()), 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- if-true/false --
  describe "(If () exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (step (If () (Read () "x") (Nop ()) (Escape () 0), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "pass: x == 0" $
        step (If () (Read () "x") (Nop ()) (Escape () 0), 0, [("x",Just 0)], [], [])
        `shouldBe` ((Escape () 0), 0, [("x",Just 0)], [], [])

      it "pass: x /= 0" $
        step (If () (Read () "x") (Nop ()) (Escape () 0), 0, [("x",Just 1)], [], [])
        `shouldBe` ((Nop ()), 0, [("x",Just 1)], [], [])

{-
  -- loop-expd --
  describe "(Loop () p)" $ do
      it "pass: lvl == 0" $
        step (Loop () (Nop ()), 0, [], [], [])
        `shouldBe` (Loop' () (Nop ()) (Nop ()), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop () (Seq () (Nop ()) (EmitInt () "z")), 3, [], [], [])
        `shouldBe`
        (Loop' () (Seq () (Nop ()) (EmitInt () "z")) (Seq () (Nop ()) (EmitInt () "z")), 3, [], [], [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop () (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"

      it "fail: isBlocked p (cannot advance)" $
        step (Loop () (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Loop' () (Fin () (Nop ())) (Fin () (Nop ())),
                     0, [], [], [])
-}

  -- loop-nop --
  describe "(Loop' () (Nop ()) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' () (Nop ()) (Nop ()), 0, [], [], [])
        `shouldBe` (Loop' () (Nop ()) (Nop ()), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' () (Nop ()) (EmitInt () "z"), 3, [], [], [])
        `shouldBe` (Loop' () (EmitInt () "z") (EmitInt () "z"), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' () (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' () (Nop ()) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Loop' () (Fin () (Nop ())) (Fin () (Nop ())), 0, [], [], [])

  -- loop-brk --
  describe "(Loop' () (Escape () 0) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' () (Escape () 0) (Nop ()), 0, [], [], [])
        `shouldBe` (Escape () 0, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' () (Escape () 0) (Seq () (EmitInt () "z") (Nop ())), 3, [], [], [])
        `shouldBe` ((Escape () 0), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' () Break (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' () (Escape () 0) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` ((Escape () 0), 0, [], [], [])

  -- loop-adv --
  describe "(Loop' () p q)" $ do
      it "pass: lvl == 0" $
        step (Loop' () (Seq () (Nop ()) (Nop ())) (Nop ()), 0, [], [], [])
        `shouldBe` (Loop' () (Nop ()) (Nop ()), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int () "z" (Loop' () (Seq () (EmitInt () "z") (Nop ())) (Escape () 0)), 3, [], [], [])
        `shouldBe` (Int () "z" (Loop' () (Seq () (CanRun () 3) (Nop ())) (Escape () 0)), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' () (Seq () (Nop ()) (Nop ())) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "fail: isBlocked p (cannot advance)" $
        forceEval (step (Loop' () (Fin () (Nop ())) (Nop ()), 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Loop' () (Seq () (Nop ()) (Nop ())) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Loop' () (Nop ()) (Fin () (Nop ())), 0, [], [], [])

  -- par-expd --
  describe "(Par () p q)" $ do
      it "pass: lvl == 0" $
        step (Par () (Nop ()) (Nop ()), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (CanRun () 0) (Nop ())), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Par () ((Nop ()) `sSeq` EmitInt () "z")  ((Nop ()) `sSeq` (Nop ())),
               3, [], [], [])
        `shouldBe` (Par' () ((Nop ()) `sSeq` EmitInt () "z")
                            (CanRun () 3 `sSeq` ((Nop ()) `sSeq` (Nop ()))), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par () (Fin () (Nop ())) (Nop ()), 0, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (CanRun () 0) (Nop ())),
                     0, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Par () (Nop ()) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (CanRun () 0) (Fin () (Nop ()))),
                    0,[],[],[])

      it "pass: isBlocked p && isBlocked q" $
        step (Par () (Fin () (Nop ())) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (CanRun () 0) (Fin () (Nop ()))),
                    0,[],[],[])

  -- par-nop1 --
  describe "(Par' () (Nop ()) q)" $ do
      it "fail: Par () does not advance on (Nop ())s" $
        forceEval (step (Par' () (Nop ()) (Nop ()), 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

{-
      it "pass: lvl > 0" $
        step (Par' () (Nop ()) (EmitInt () "z"), 3, [], [], [])
        `shouldBe` (Par' () (Nop ()) (EmitInt () "z"), 2, [], [], [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        forceEval (step (Par' () (Nop ()) (Fin () (Nop ())), 0, [], [], []))
        --`shouldBe` (Fin () (Nop ()), 0, [], [], [])
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: q == (Nop ())" $
        forceEval (step (Par' () (Nop ()) (Nop ()), 0, [], [], []))
        --`shouldBe` ((Nop ()), 0, [], [], [])
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: q == (Escape () 0)" $
        step (Par' () (AwaitExt () "FOREVER") (Escape () 0), 0, [], [], [])
        `shouldBe` ((Seq () (Nop ()) (Escape () 0)), 0, [], [], [])

  -- par-brk1 --
  describe "(Par' () (Escape () 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitExt () "A") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitInt () "a") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 3, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Escape () 0) (Var () ("_",Nothing) (Nop ())), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin () (Seq () (Nop ()) (Nop ())) in
          (clear q `shouldBe` (Seq () (Nop ()) (Nop ())))
          >>                    -- clear q == (Nop ()); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' () (AwaitExt () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitInt () "b"))
                          (Par' () (Fin () (EmitInt () "c" `sSeq` EmitInt () "d"))
                            (AwaitInt () "a" `sSeq` Fin () (EmitInt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitInt () "b" `sSeq`
                      (EmitInt () "c" `sSeq` EmitInt () "d") `sSeq` (Nop ()) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: clear Par'" $
        (step (Par' () (Escape () 0) (Nop ()), 0, [], [], []))
        `shouldBe` (Seq () (Nop ()) (Escape () 0), 0, [], [], [])

      it "fail: q == (Escape () 0) (invalid clear)" $
        forceEval (step (Par' () (Escape () 0) (Escape () 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- par-nop2 --
  describe "(Par' () p (Nop ()))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        step (Par' () (Fin () (Nop ())) (AwaitExt () "FOREVER"), 1, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (AwaitExt () "FOREVER"),0,[],[],[])

      it "pass: lvl > 0 && isBlocked p" $
        step (Par' () (Seq () (Fin () (Nop ())) (Nop ())) (AwaitExt () "FOREVER"), 3, [], [], [])
        `shouldBe` (Par' () (Seq () (Fin () (Nop ())) (Nop ())) (AwaitExt () "FOREVER"),2,[],[],[])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Fin () (Nop ())) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: p == (Nop ())" $
        step (Par' () (AwaitExt () "FOREVER") (AwaitExt () "FOREVER"), 1, [], [], [])
        `shouldBe` (Par' () (AwaitExt () "FOREVER") (AwaitExt () "FOREVER"),0,[],[],[])

  -- par-brk2 --
  describe "(Par' () p (Escape () 0))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt () "b") in
          (clear p `shouldBe` (Nop ()))
          >>                    -- clear p == (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
           `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin () (Seq () (Nop ()) (Nop ())) in
          (clear p `shouldBe` (Seq () (Nop ()) (Nop ())))
          >>
          (step (Par' () p (Escape () 0), 3, [], [], [])
           `shouldBe` (Seq () (clear p) (Escape () 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Fin () (Nop ())) (Escape () 0), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Par' () (AwaitExt () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitInt () "b"))
                          (Par' () (Fin () (EmitInt () "c" `sSeq` EmitInt () "d"))
                            (AwaitInt () "a" `sSeq` Fin () (EmitInt () "e"))))
            clear_p = (Nop ()) `sSeq` EmitInt () "b" `sSeq`
                      (EmitInt () "c" `sSeq` EmitInt () "d") `sSeq` (Nop ()) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "pass: p == (Nop ())" $
        step (Par' () (AwaitExt () "FOREVER") (Escape () 0), 0, [], [], [])
        `shouldBe` (Seq () (Nop ()) (Escape () 0), 0, [], [], [])

      it "fail: p == (Escape () 0) (invalid clear)" $
        forceEval (step (Par' () (Escape () 0) (Escape () 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- par-adv --
  describe "(Par' () p q)" $ do
      it "pass: lvl == 0" $
        step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Escape () 0) (Escape () 0)), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (Escape () 0) (Escape () 0)), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Int () "y" (Int () "z" (Par' () (Seq () (EmitInt () "z") (Nop ())) (Seq () (EmitInt () "y") (Nop ())))),
               3, [], [], [])
        `shouldBe` (Int () "y" (Int () "z" (Par' () (Seq () (CanRun () 3) (Nop ())) (Seq () (EmitInt () "y") (Nop ())))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Nop ()) (Nop ())),
                         0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' () (Fin () (Nop ())) (Seq () (Int () "z" (EmitInt () "z")) (Nop ())),
               3, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (Int () "z" (CanRun () 3)) (Nop ())),
                     4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Int () "z" (Par' () (EmitInt () "z") (AwaitInt () "z")), 3, [], [], [])
        `shouldBe` (Int () "z" (Par' () (CanRun () 3) (Nop ())), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' () (AwaitInt () "d") (AwaitInt () "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- par-expd --
  describe "(Par () p q)" $ do
      it "pass: lvl == 0" $
        step (Par () (Nop ()) (Nop ()), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (CanRun () 0) (Nop ())),
                    0,[],[],[])

      it "pass: lvl > 0" $
        step (Par () (Seq () (Nop ()) (EmitInt () "z")) (Seq () (Nop ()) (Nop ())), 3, [], [], [])
        `shouldBe` (Par' () (Seq () (Nop ()) (EmitInt () "z")) (Seq () (CanRun () 3) (Seq () (Nop ()) (Nop ()))),
                    3,[],[],[])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par () (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par () (Fin () (Nop ())) (Nop ()), 0, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (CanRun () 0) (Nop ())),
                    0,[],[],[])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Par () (Nop ()) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (CanRun () 0) (Fin () (Nop ()))),
                    0,[],[],[])

      it "pass: isBlocked p && isBlocked q" $
        step (Par () (Fin () (Nop ())) (Fin () (Nop ())), 0, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (CanRun () 0) (Fin () (Nop ()))),
                    0,[],[],[])

  -- or-nop1 --
  describe "(Par' () (Nop ()) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt () "a") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitInt () "z") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 1) q, 3, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 1), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' (Nop ()) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = (Fin () (Nop ())) in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' () (AwaitExt () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitInt () "b"))
                          (Par' () (Fin () (EmitInt () "c" `sSeq` EmitInt () "d"))
                            (AwaitInt () "a" `sSeq` Fin () (EmitInt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitInt () "b" `sSeq`
                      (EmitInt () "c" `sSeq` EmitInt () "d") `sSeq` (Nop ()) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

  -- or-brk1 --
  describe "(Par' () (Escape () 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInt () "a") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "transit: lvl > 0" $
        let q = (AwaitInt () "z") in
          (clear q`shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 3, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Escape () 0) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin () (Seq () (Nop ()) (Nop ())) in
          (clear q `shouldBe` (Seq () (Nop ()) (Nop ())))
          >>                    -- clear q == (Nop ()); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' () (AwaitExt () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitInt () "b"))
                          (Par' () (Fin () (EmitInt () "c" `sSeq` EmitInt () "d"))
                            (AwaitInt () "a" `sSeq` Fin () (EmitInt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitInt () "b" `sSeq`
                      (EmitInt () "c" `sSeq` EmitInt () "d") `sSeq` (Nop ()) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () clear_q (Escape () 0), 0, [], [], []))

  -- or-nop2 --
  describe "(Par' () p (Nop ()))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin () (Nop ())) in
          (clear p `shouldBe` (Nop ()))
          >>                    -- clear p == (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq () (Fin () (Nop ())) (Nop ()) in
          (clear p `shouldBe` (Nop ()))
          >>                    -- clear p == (Nop ())
          (step (Par' () p (Escape () 0), 3, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Fin () (Nop ())) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- or-brk2 --
  describe "(Par' () p (Escape () 0))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitInt () "b") in
          (clear p `shouldBe` (Nop ()))
          >>                    -- clear p == (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
           `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin () (Seq () (Nop ()) (Nop ())) in
          (clear p `shouldBe` Seq () (Nop ()) (Nop ()))
          >>                    -- clear p == (Nop ()); (Nop ())
          (step (Par' () p (Escape () 0), 3, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Fin () (Nop ())) (Escape () 0), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Par' () (AwaitExt () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitInt () "b"))
                          (Par' () (Fin () (EmitInt () "c" `sSeq` EmitInt () "d"))
                            (AwaitInt () "a" `sSeq` Fin () (EmitInt () "e"))))
            clear_p = (Nop ()) `sSeq` EmitInt () "b" `sSeq`
                      (EmitInt () "c" `sSeq` EmitInt () "d") `sSeq` (Nop ()) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "fail: p == (Nop ()) (invalid clear)" $
        (step (Par' () (AwaitExt () "FOREVER") (Escape () 0), 0, [], [], []))
        `shouldBe` (Seq () (Nop ()) (Escape () 0),0,[],[],[])

      it "fail: p == (Escape () 0) (invalid clear)" $
        forceEval (step (Par' () (Escape () 0) (Escape () 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-adv --
  describe "(Par' () p q)" $ do
      it "pass: lvl == 0" $
        step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Escape () 0) (Escape () 0)), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (Escape () 0) (Escape () 0)), 0, [], [], [])

      it "psas: lvl > 0" $
        step (Par' () (Int () "z" (Seq () (EmitInt () "z") (Nop ()))) (Int () "y" (Seq () (EmitInt () "y") (Nop ()))),
               3, [], [], [])
        `shouldBe` (Par' () (Int () "z" (Seq () (CanRun () 3) (Nop ()))) (Int () "y" (Seq () (EmitInt () "y") (Nop ()))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Nop ()) (Nop ())),
                          0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' () (Fin () (Nop ())) (Int () "z" (Seq () (EmitInt () "z") (Nop ()))), 3, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Int () "z" (Seq () (CanRun () 3) (Nop ()))), 4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Int () "z" (Par' () (EmitInt () "z") (AwaitInt () "z")), 3, [], [], [])
        `shouldBe` (Int () "z" (Par' () (CanRun () 3) (Nop ())), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' () (AwaitInt () "d") (AwaitInt () "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- pause --
  describe "(Pause () var p)" $ do
      it "pass: (Nop ())" $
        step (Var () ("x",Nothing) (Pause () "x" (Nop ())), 0, [], [], [])
        `shouldBe` (Var () ("x",Nothing) (Nop ()), 0, [], [], [])

      it "pass: awake" $
        step (Var () ("x",(Just 0)) (Pause () "x" (Int () "e" (Par' () (AwaitInt () "e") (EmitInt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 0)) (Pause () "x" (Int () "e" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "pass: awake - nested reaction inside Pause" $
        step (Var () ("x",(Just 1)) (Pause () "x" (Int () "e" (Par' () (AwaitInt () "e") (EmitInt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 1)) (Pause () "x" (Int () "e" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "pass: don't awake - nested reaction outside Pause" $
        step (Var () ("x",(Just 1)) (Int () "e" (Pause () "x" (Par' () (AwaitInt () "e") (EmitInt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 1)) (Int () "e" (Pause () "x" (Par' () (AwaitInt () "e") (CanRun () 0)))),1,[],[],[])

      it "pass: awake - nested reaction outside Pause" $
        step (Var () ("x",(Just 0)) (Int () "e" (Pause () "x" (Par' () (AwaitInt () "e") (EmitInt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 0)) (Int () "e" (Pause () "x" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "fail: undeclared var" $
        forceEval (step (Int () "e" (Pause () "x" (EmitInt () "e")), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninit var" $
        forceEval (step (Int () "e" (Var () ("x",Nothing) (Pause () "x" (EmitInt () "e"))), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (program is blocked)" $ do

      stepsItPass
        (AwaitExt () "A", 0, [], [], [])
        (AwaitExt () "A", 0, [], [], [])

      stepsItPass
        (AwaitInt () "a", 0, [], [], [])
        (AwaitInt () "a", 0, [], [], [])

      stepsItPass
        (Seq () (AwaitInt () "a") (Nop ()), 0, [], [], [])
        (Seq () (AwaitInt () "a") (Nop ()), 0, [], [], [])

      stepsItPass
        (Every () "A" (Nop ()), 0, [], [], [])
        (Every () "A" (Nop ()), 0, [], [], [])

      stepsItPass
        (Pause () "a" (AwaitExt () ""), 0, [], [], [])
        (Pause () "a" (AwaitExt () ""), 0, [], [], [])

      stepsItPass
        (Fin () (Seq () (Nop ()) (Nop ())), 0, [], [], [])
        (Fin () (Seq () (Nop ()) (Nop ())), 0, [], [], [])

      stepsItPass
        (Par' () (AwaitExt () "A") (Fin () (Nop ())), 0, [], [], [])
        (Par' () (AwaitExt () "A") (Fin () (Nop ())), 0, [], [], [])

      stepsItPass
        (Par' () (AwaitExt () "A") (Fin () (Nop ())), 0, [], [], [])
        (Par' () (AwaitExt () "A") (Fin () (Nop ())), 0, [], [], [])

{-
      stepsItFail "step: cannot advance"
        (CanRun () 5, 0, [], [], [])
-}

    describe "zero steps (no step-rule applies)" $ do

      stepsItPass
        ((Nop ()), 0, [], [], [])
        ((Nop ()), 0, [], [], [])

      stepsItPass
        ((Escape () 0), 0, [], [], [])
        ((Escape () 0), 0, [], [], [])

    describe "one+ steps" $ do

      stepsItPass
        (Var () ("x",Nothing) (Write () "x" (Const () 0)), 3, [], [], [])
        ((Nop ()), 0, [], [], [])

      stepsItPass
        (Int () "z" (EmitInt () "z"), 3, [], [], [])
        ((Nop ()), 0, [], [], [])
        --(Int () "z" (CanRun () 3), 4, [], [], [])

      stepsItPass
        (CanRun () 3, 3, [], [], [])
        ((Nop ()), 0, [], [], [])

      stepsItPass
        ((Nop ()) `sSeq` (Nop ()) `sSeq` (Nop ()) `sSeq` (Escape () 0) `sSeq` (Nop ()), 0, [], [], [])
        ((Escape () 0), 0, [], [], [])

      stepsItPass
        (Loop' () (Escape () 0) (Escape () 0) `sSeq` (Nop ()) `sSeq` (Nop ()) `sSeq` (Int () "z" (EmitInt () "z")) `sSeq` (Escape () 0),
          3, [], [], [])
        ((Escape () 0), 0, [], [], [])

      stepsItPass
        (Loop' () (Escape () 0) (Escape () 0), 3, [], [], [])
        (Escape () 0, 0, [], [], [])

      stepsItPass
        (Trap () (Loop' () (Escape () 0) (Escape () 0)), 3, [], [], [])
        ((Nop ()), 0, [], [], [])

      stepsItPass
        ((Seq () (Trap () (Loop' () (Escape () 0) (Escape () 0))) (Nop ())), 3, [], [], [])
        (Nop (),0,[],[],[])

      stepsItPass
        ((Seq () (Int () "z" (EmitInt () "z")) (Nop ())), 3, [], [], [])
        (Nop (),0,[],[],[])

      it "nop par nop" $ do
        isBlocked 0 (Par' () (Nop ()) (Nop ()))
          `shouldBe` True
      it "nop par nop" $ do
        isReducible (Par' () (Nop ()) (Nop ()), 0, [], [], [])
          `shouldBe` False

      stepsItPass
        ((Nop ()) `sPar` (Nop ()), 3, [], [], [])
        (Par' () (Nop ()) (Nop ()),0,[],[],[])

      it "blocked/par" $ do
        isBlocked 3 (Par' () (Nop ()) (Seq () (CanRun () 3) (Seq () (Int () "z" (EmitInt () "z")) (Nop ()))))
        `shouldBe` False

      stepsItPass
        ((Seq () (Trap () (Loop' () (Escape () 0) (Escape () 0))) (Nop ())) `sPar` (Seq () (Int () "z" (EmitInt () "z")) (Nop ())), 3, [], [], [])
        (Par' () (Nop ()) (Nop ()),0,[],[],[])

      stepsItPass
        (Seq () (Trap () (Trap () (Loop' () (Escape () 1) (Escape () 1)))) (Nop ()) `sPar` Seq () (Int () "z" (EmitInt () "z")) (Nop ()), 3, [], [], [])
        (Par' () (Nop ()) (Nop ()),0,[],[],[])

      stepsItPass
        (Trap () (Loop' ()
          (((Nop ()) `sSeq` (AwaitInt () "d")) `sPar`
            ((AwaitExt () "M") `sPar` ((Nop ()) `sSeq` (Escape () 0))))
          (((Nop ()) `sSeq` (AwaitInt () "d")) `sPar`
            ((AwaitExt () "M") `sPar` ((Nop ()) `sSeq` (Escape () 0))))), 0, [], [], [])
        ((Nop ()), 0, [], [], [])

  --------------------------------------------------------------------------
  describe "out1" $ do

{-
    -- push --
    describe "push" $ do
      it "pass: lvl == 0" $
        out1 ((Nop ()), 0, Just "b", [], [])
        `shouldBe` ((Nop ()), 1, [], [], [])

      it "pass: lvl > 0" $
        out1 (Seq () (AwaitInt () "b") Break, 3, Just "b", [], [])
        `shouldBe` (Seq () (Nop ()) Break, 4, [], [], [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq () (AwaitInt () "c") Break, 3, Just "b", [], [])
        `shouldBe` (Seq () (AwaitInt () "c") Break, 4, [], [], [])

    -- pop --
    describe "pop" $ do
      it "fail: lvl == 0 (cannot advance)" $
        forceEval (out1 ((Nop ()), 0, [], [], []))
        `shouldThrow` errorCall "outPop: cannot advance"

      it "pass: lvl > 0 && not (isReducible p)" $
        out1 ((Nop ()), 33, [], [], [])
        `shouldBe` ((Nop ()), 32, [], [], [])

      it "pass: lvl > 0 && not (nstReducible p)" $
        forceEval (out1 (Seq () (Nop ()) (Nop ()), 1, [], [], []))
        `shouldThrow` errorCall "outPop: cannot advance"
-}

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (no out-rule applies)" $ do
      it "pass: lvl == 0 && not (isReducible p)" $
        let d = ((Nop ()), 0, [], [], []) in
          (steps d `shouldBe` d)
          >> ((isReducible d) `shouldBe` False)
          -- >> (isReducible d `shouldBe` True)

      it "pass: lvl == 0 && not (not (isReducible p))" $
        let d = (Seq () (Nop ()) (Nop ()), 0, [], [], []) in
          (steps d `shouldBe` ((Nop ()),0,[],[], []))
          >> ((isReducible d) `shouldBe` True)
          -- >> (isReducible d `shouldBe` False)

    describe "one+ pops" $ do
      it "pass: lvl > 0" $
        let d = (Int () "x" (EmitInt () "x"), 0, [], [], [])
            d' = ((Nop ()), 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl>0, but `(Nop ())`" $
        let d = ((Nop ()), 13, [], [], []) in
          (steps d `shouldBe` ((Nop ()), 0, [], [], []))
          >> (isReducible d `shouldBe` True)

    describe "one push followed by one+ pops" $ do
      it "pass: lvl == 0 (do nothing)" $ -- CHECK THIS! --
        let d = (bcast "c" [] (AwaitInt () "d"), 0, [], [], [])
            d' = (AwaitInt () "d", 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl > 0, but `(Nop ())`" $
        let d = (bcast "d" [] (AwaitInt () "d"), 88, [], [], [])
            d' = ((Nop ()), 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      (Int () "d"
        (Par ()
          (EmitInt () "d")
          (((Nop ()) `sSeq` AwaitInt () "d") `sPar` ((Nop ()) `sSeq` Fin () (Nop ()))
      )), "_", [])
      (Int () "d" (Par' () (Nop ()) (Par' () (AwaitInt () "d") (Fin () (Nop ())))),[],[])

    reactionItPass
      (Int () "d" (((Nop ()) `sSeq` AwaitInt () "d") `sPar` ((Nop ()) `sSeq` EmitInt () "d")), "_", [])
      (Int () "d" (Par' () (Nop ()) (Nop ())),[],[])

    reactionItPass
      (Var () ("x",(Just 0)) (Int () "e" (Pause () "x" (Trap () (Par () (Seq () (AwaitInt () "e") (Escape () 0)) (EmitInt () "e"))))), "_", [])
      ((Nop ()), [], [])

    reactionItPass
      (Var () ("x",(Just 1)) (Int () "e" (Pause () "x" (Trap () (Par () (Seq () (AwaitInt () "e") (Escape () 0)) (EmitInt () "e"))))), "_", [])
      (Var () ("x",Just 1) (Int () "e" (Pause () "x" (Trap () (Par' () (Seq () (AwaitInt () "e") (Escape () 0)) (Nop ()))))),[],[])

  --------------------------------------------------------------------------
  describe "compile_run" $ do

    evalProgItSuccess (11,[[]])
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
            G.Escape () 0))

    evalProgItFail ["escape: orphan `escape` statement","trap: missing `escape` statement","await: unreachable statement"]
      [] (G.Escape () 1)

    evalProgItFail ["declaration: variable '_ret' is already declared"]
      [] (G.Var () "a"
           (G.Var () "_ret"
             (G.Write () "a" (Const () 1) `G.sSeq`
              G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
              G.Escape () 0)))

    evalProgItFail ["declaration: variable '_ret' is already declared"]
      [] (G.Write () "_ret" (Const () 1) `G.sSeq`
          G.Var () "_ret" (G.Write () "_ret" (Const () 99)) `G.sSeq`
          G.Escape () 0)

    evalProgItSuccess (11,[[]])
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Var () "b" (G.Write () "b" (Const () 99)) `G.sSeq`
            G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
            G.Escape () 0))

    evalProgItFail ["declaration: variable 'a' is already declared"]
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Var () "a" (G.Write () "a" (Const () 99)) `G.sSeq`
            G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
            G.Escape () 0))

    evalProgItSuccess (2,[[]])
      [] (G.Write () "_ret" (Const () 1) `G.sSeq`
          G.Var () "_" (G.Write () "_ret" (Const () 2)) `G.sSeq`
          G.Escape () 0)

    evalProgItSuccess (11,[[]])
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Trap () (G.Par ()
             (G.Var () "b" (G.Write () "b" (Const () 99) `G.sSeq` G.AwaitExt () "A") `G.sSeq` (G.AwaitExt () "FOREVER"))
             (G.Escape () 0)) `G.sSeq`
           G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
           G.Escape () 0))

    evalProgItFail ["trap: missing `escape` statement"]
      [] (G.Trap () (G.Par ()
           (G.Var () "x" (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
           (G.Escape () 1)))

    evalProgItSuccess (1,[[]])
      [] (G.Seq () (G.Trap () (G.Par ()
           (G.Var () "x" (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
           (G.Escape () 0))) (G.Escape () 0))

    evalProgItFail ["loop: `loop` never iterates","declaration: variable 'a' is already declared"]
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Trap () (G.Loop () (G.Par ()
                  (G.Var () "a" (G.Write () "a" (Const () 99) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
                  (G.Escape () 0))) `G.sSeq`
             G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
            G.Escape () 0))

    evalProgItSuccess (11,[[]])
      [] (G.Var () "a"
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Trap () (G.Par ()
                  (G.Var () "b" (G.Write () "b" (Const () 99) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
                  (G.Escape () 0)) `G.sSeq`
            G.Write () "_ret" (Read () "a" `eAdd` Const () 10) `G.sSeq`
            G.Escape () 0))

    evalProgItFail ["loop: `loop` never iterates"]
      [] (G.Seq () (G.Trap () (G.Loop () (G.Par ()
                 (G.Var () "x" (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
                 (G.Escape () 0)))) (G.Escape () 0))

    evalProgItSuccess (1,[[]])
      [] (G.Seq () (G.Trap () (G.Par ()
                 (G.Var () "x" (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "FOREVER"))
                 (G.Escape () 0))) (G.Escape () 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write () "_ret" (Const () 1)) `G.sSeq`
      (G.Int () "a"
        (G.Trap ()
        (G.Par ()
          ((G.AwaitInt () "a") `G.sSeq` (G.Write () "_ret" (Const () 5)) `G.sSeq` (G.Escape () 0))
          ((G.EmitInt () "a") `G.sSeq` G.AwaitExt () "FOREVER")))) `G.sSeq`
      (G.Escape () 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write () "_ret" (Const () 1)) `G.sSeq`
      (G.Int () "a"
        (G.Trap () (G.Par ()
          ((G.AwaitInt () "a") `G.sSeq` (G.Write () "_ret" (Const () 5)) `G.sSeq` (G.Escape () 0))
          (G.Seq () (G.Trap () (G.Par () (G.Fin () (G.EmitInt () "a")) (G.Escape () 0))) (G.Escape () 0)))
      )) `G.sSeq` (G.Escape () 0))

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
    evalProgItSuccess (99,[[]]) [] (
      (G.Var () "x" (
        (G.Write () "x" (Const () 10)) `G.sSeq`
        (G.Trap () (G.Par ()
          (G.Var () "y" (G.AwaitExt () "FOREVER"))
          (G.Seq () (G.Write () "x" (Const () 99)) (G.Escape () 0))
        )) `G.sSeq`
        (G.Write () "_ret" (Read () "x")) `G.sSeq`
        (G.Escape () 0)
      )))

    evalProgItSuccess (99,[[],[]]) ["A"]
      (G.Seq () (G.Seq ()
        (G.Var () "x"
          (G.Seq ()
            (G.Write () "x" (Const () 1))
            (G.Int () "e"
              (G.Trap () (G.Par ()
                (G.Seq () (G.AwaitExt () "A") (G.Seq () (G.Write () "x" (Const () 0)) (G.Seq () (G.EmitInt () "e") (G.AwaitExt () "FOREVER"))))
                (G.Seq () (G.Pause () "x" (G.Trap () (G.Par () (G.Seq () (G.AwaitInt () "e") (G.Escape () 0)) ((G.EmitInt () "e") `G.sSeq` (G.AwaitExt () "FOREVER"))))) (G.Escape () 0)))))))
        (G.Write () "_ret" (Const () 99))) (G.Escape () 0))

    -- multiple inputs

    evalProgItSuccess (1,[[],[]])
      ["A"] (G.AwaitExt () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` (G.Escape () 0))

    evalProgItFail ["program didn't terminate"]
      [] (G.AwaitExt () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    evalProgItFail ["program didn't terminate"]
      ["B"] (G.AwaitExt () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    evalProgItFail ["pending inputs"]
      ["A","A"] (G.AwaitExt () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    evalProgItSuccess (1,[[],[],[]])
      ["A","B"] (G.AwaitExt () "A" `G.sSeq` G.AwaitExt () "B" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    evalProgItSuccess (1,[[]]) [] (G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    -- multiple outputs

    evalProgItSuccess (1,[[],[("O",Nothing)],[("O",Nothing)],[]]) ["I","I","F"]
      (G.Seq () (G.Seq () (G.Write () "_ret" (Const () 1))
        (G.Trap () (G.Par () (G.Seq () (G.AwaitExt () "F") (G.Escape () 0)) (G.Every () "I" (G.EmitExt () "O" Nothing))))) (G.Escape () 0))

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

        evalProgItSuccess (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg prog) res (show outss)) $
            (compile_run prog hist `shouldBe` Right (res,outss)))

        evalProgItFail err hist prog =
          (it (printf "pass: %s | %s ***%s" (show hist) (G.showProg prog) (show err)) $
            (compile_run prog hist `shouldBe` Left err))
