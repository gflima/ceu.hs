module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals (Ann(..), Type(..))
import Ceu.Grammar.Ann.Unit
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Exp, Stmt, and Desc as datatypes that can be fully evaluated.
instance NFData (Exp ann) where
  rnf (RawE  _ _)   = ()
  rnf (Const _ _)   = ()
  rnf (Read  _ _)   = ()
  rnf (Unit  _)     = ()
  rnf (Tuple _ _)   = ()
  rnf (Call  _ _ _) = ()

instance NFData (Stmt ann) where
  rnf (Write _ _ expr) = rnf expr
  rnf (AwaitInp _ _)   = ()
  rnf (AwaitEvt _ _)   = ()
  rnf (EmitEvt _ _)    = ()
  rnf (If _ expr p q)  = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq _ p q)      = rnf p `deepseq` rnf q
  rnf (Every _ _ p)    = rnf p
  rnf (Par _ p q)      = rnf p `deepseq` rnf q
  rnf (Pause _ _ p)    = rnf p
  rnf (Fin _ p)        = rnf p
  rnf (Trap _ p)       = rnf p
  rnf (Escape _ _)     = ()
  rnf (Nop _)          = ()
  rnf (Error _ _)      = ()
  rnf (CanRun _ _)     = ()
  rnf (Var _ _ p)      = rnf p
  rnf (Evt _ _ p)      = rnf p
  rnf (Loop' _ p q)    = rnf p
  rnf (Par' _ p q)     = rnf p `deepseq` rnf q

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
          varsEval vars (Call () "add" (Tuple () [(Call () "sub" (Tuple () [(Read () "x"),(Const () 3)])),(Call () "umn" (Read () "y"))]))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let vars = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval vars (Call () "add" (Tuple () [(Call () "sub" (Tuple () [(Read () "x"),(Const () 3)])),(Call () "umn" (Read () "y"))]))
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
        (forceEval $ step (EmitEvt () "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "fail: TODO: ok" $
        (forceEval $ step (Var () ("_ret",Nothing) ((Write () "_ret" (Const () 25)) `sSeq` (EmitEvt () "a")), 0, [], [], []))
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
            (Write () "y" (Call () "add" (Tuple () [(Read () "x"),(Const () 2)])))), 0, [], [], []))
        `shouldBe` (Var () ("x",(Just 1)) (Var () ("y",(Just 3)) (Nop ())),0,[],[], [])

      it "pass: [x=1,y=?] y=x+2" $
        step
        (Var () ("x",(Just 1))
        (Var () ("y",Nothing)
          (Write () "y" (Call () "add" (Tuple () [(Read () "x"),(Const () 2)])))), 0, [], [], [])
        `shouldBe`
        (Var () ("x",(Just 1))
        (Var () ("y",(Just 3)) (Nop ())), 0, [], [], [])

      it "pass: [x=?] x=-(5+1)" $
        step
        (Var () ("x",(Just 0))
          (Write () "x" (Call () "umn" (Call () "add" (Tuple () [(Const () 5),(Const () 1)])))), 0, [], [], [])
        `shouldBe`
        (Var () ("x",(Just (-6))) (Nop ()), 0, [], [], [])

    -- emit-int --
  describe "(EmitEvt () e')" $ do
      it "fail: {? emit a}" $
        forceEval (step (EmitEvt () "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: lvl == 0" $
        step (Evt () "a" (EmitEvt () "a"), 0, [], [], [])
        `shouldBe` (Evt () "a" (CanRun () 0), 1, [], [], [])

      it "pass: pop" $
        (step (Evt () "a" (CanRun () 0), 1, [], [], []))
        `shouldBe` (Evt () "a" (CanRun () 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Evt () "b" (EmitEvt () "b"), 3, [], [], [])
        `shouldBe` (Evt () "b" (CanRun () 3), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (EmitEvt () "b", 3, Just "b", [], []))
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
        step (Seq () (Escape () 0) (EmitEvt () "z"), 3, [], [], [])
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
        step (Seq () (Seq () (Evt () "z" (EmitEvt () "z")) (Nop ())) (Nop ()), 3, [], [], [])
        `shouldBe` (Seq () (Seq () (Evt () "z" (CanRun () 3)) (Nop ())) (Nop ()), 4, [], [], [])

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
        step (Loop () (Seq () (Nop ()) (EmitEvt () "z")), 3, [], [], [])
        `shouldBe`
        (Loop' () (Seq () (Nop ()) (EmitEvt () "z")) (Seq () (Nop ()) (EmitEvt () "z")), 3, [], [], [])

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
        step (Loop' () (Nop ()) (EmitEvt () "z"), 3, [], [], [])
        `shouldBe` (Loop' () (EmitEvt () "z") (EmitEvt () "z"), 3, [], [], [])

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
        step (Loop' () (Escape () 0) (Seq () (EmitEvt () "z") (Nop ())), 3, [], [], [])
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
        step (Evt () "z" (Loop' () (Seq () (EmitEvt () "z") (Nop ())) (Escape () 0)), 3, [], [], [])
        `shouldBe` (Evt () "z" (Loop' () (Seq () (CanRun () 3) (Nop ())) (Escape () 0)), 4, [], [], [])

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
        step (Par () ((Nop ()) `sSeq` EmitEvt () "z")  ((Nop ()) `sSeq` (Nop ())),
               3, [], [], [])
        `shouldBe` (Par' () ((Nop ()) `sSeq` EmitEvt () "z")
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
        step (Par' () (Nop ()) (EmitEvt () "z"), 3, [], [], [])
        `shouldBe` (Par' () (Nop ()) (EmitEvt () "z"), 2, [], [], [])

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
        step (Par' () (Halt ()) (Escape () 0), 0, [], [], [])
        `shouldBe` ((Seq () (Nop ()) (Escape () 0)), 0, [], [], [])

  -- par-brk1 --
  describe "(Par' () (Escape () 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInp () "A") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitEvt () "a") in
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
        let q = Par' () (AwaitInp () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitEvt () "b"))
                          (Par' () (Fin () (EmitEvt () "c" `sSeq` EmitEvt () "d"))
                            (AwaitEvt () "a" `sSeq` Fin () (EmitEvt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitEvt () "b" `sSeq`
                      (EmitEvt () "c" `sSeq` EmitEvt () "d") `sSeq` (Nop ()) in
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
        step (Par' () (Fin () (Nop ())) (Halt ()), 1, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Halt ()),0,[],[],[])

      it "pass: lvl > 0 && isBlocked p" $
        step (Par' () (Seq () (Fin () (Nop ())) (Nop ())) (Halt ()), 3, [], [], [])
        `shouldBe` (Par' () (Seq () (Fin () (Nop ())) (Nop ())) (Halt ()),2,[],[],[])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Fin () (Nop ())) (Nop ()), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: p == (Nop ())" $
        step (Par' () (Halt ()) (Halt ()), 1, [], [], [])
        `shouldBe` (Par' () (Halt ()) (Halt ()),0,[],[],[])

  -- par-brk2 --
  describe "(Par' () p (Escape () 0))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitEvt () "b") in
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
        let p = Par' () (AwaitInp () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitEvt () "b"))
                          (Par' () (Fin () (EmitEvt () "c" `sSeq` EmitEvt () "d"))
                            (AwaitEvt () "a" `sSeq` Fin () (EmitEvt () "e"))))
            clear_p = (Nop ()) `sSeq` EmitEvt () "b" `sSeq`
                      (EmitEvt () "c" `sSeq` EmitEvt () "d") `sSeq` (Nop ()) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "pass: p == (Nop ())" $
        step (Par' () (Halt ()) (Escape () 0), 0, [], [], [])
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
        step (Evt () "y" (Evt () "z" (Par' () (Seq () (EmitEvt () "z") (Nop ())) (Seq () (EmitEvt () "y") (Nop ())))),
               3, [], [], [])
        `shouldBe` (Evt () "y" (Evt () "z" (Par' () (Seq () (CanRun () 3) (Nop ())) (Seq () (EmitEvt () "y") (Nop ())))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Nop ()) (Nop ())),
                         0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' () (Fin () (Nop ())) (Seq () (Evt () "z" (EmitEvt () "z")) (Nop ())),
               3, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Seq () (Evt () "z" (CanRun () 3)) (Nop ())),
                     4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Evt () "z" (Par' () (EmitEvt () "z") (AwaitEvt () "z")), 3, [], [], [])
        `shouldBe` (Evt () "z" (Par' () (CanRun () 3) (Nop ())), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' () (AwaitEvt () "d") (AwaitEvt () "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- par-expd --
  describe "(Par () p q)" $ do
      it "pass: lvl == 0" $
        step (Par () (Nop ()) (Nop ()), 0, [], [], [])
        `shouldBe` (Par' () (Nop ()) (Seq () (CanRun () 0) (Nop ())),
                    0,[],[],[])

      it "pass: lvl > 0" $
        step (Par () (Seq () (Nop ()) (EmitEvt () "z")) (Seq () (Nop ()) (Nop ())), 3, [], [], [])
        `shouldBe` (Par' () (Seq () (Nop ()) (EmitEvt () "z")) (Seq () (CanRun () 3) (Seq () (Nop ()) (Nop ()))),
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
        let q = (AwaitEvt () "a") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitEvt () "z") in
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
        let q = Par' () (AwaitInp () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitEvt () "b"))
                          (Par' () (Fin () (EmitEvt () "c" `sSeq` EmitEvt () "d"))
                            (AwaitEvt () "a" `sSeq` Fin () (EmitEvt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitEvt () "b" `sSeq`
                      (EmitEvt () "c" `sSeq` EmitEvt () "d") `sSeq` (Nop ()) in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
            `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

  -- or-brk1 --
  describe "(Par' () (Escape () 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitEvt () "a") in
          (clear q `shouldBe` (Nop ()))
          >>                    -- clear q == (Nop ())
          (step (Par' () (Escape () 0) q, 0, [], [], [])
           `shouldBe` (Seq () (clear q) (Escape () 0), 0, [], [], []))

      it "transit: lvl > 0" $
        let q = (AwaitEvt () "z") in
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
        let q = Par' () (AwaitInp () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitEvt () "b"))
                          (Par' () (Fin () (EmitEvt () "c" `sSeq` EmitEvt () "d"))
                            (AwaitEvt () "a" `sSeq` Fin () (EmitEvt () "e"))))
            clear_q = (Nop ()) `sSeq` EmitEvt () "b" `sSeq`
                      (EmitEvt () "c" `sSeq` EmitEvt () "d") `sSeq` (Nop ()) in
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
        let p = (AwaitEvt () "b") in
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
        let p = Par' () (AwaitInp () "A" `sSeq` Fin () (Nop ()))
                    (Par' () (Fin () (EmitEvt () "b"))
                          (Par' () (Fin () (EmitEvt () "c" `sSeq` EmitEvt () "d"))
                            (AwaitEvt () "a" `sSeq` Fin () (EmitEvt () "e"))))
            clear_p = (Nop ()) `sSeq` EmitEvt () "b" `sSeq`
                      (EmitEvt () "c" `sSeq` EmitEvt () "d") `sSeq` (Nop ()) in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == (Nop ()); Emit1; (Emit2; Emit3); (Nop ())
          (step (Par' () p (Escape () 0), 0, [], [], [])
            `shouldBe` (Seq () (clear p) (Escape () 0), 0, [], [], []))

      it "fail: p == (Nop ()) (invalid clear)" $
        (step (Par' () (Halt ()) (Escape () 0), 0, [], [], []))
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
        step (Par' () (Evt () "z" (Seq () (EmitEvt () "z") (Nop ()))) (Evt () "y" (Seq () (EmitEvt () "y") (Nop ()))),
               3, [], [], [])
        `shouldBe` (Par' () (Evt () "z" (Seq () (CanRun () 3) (Nop ()))) (Evt () "y" (Seq () (EmitEvt () "y") (Nop ()))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' () (Seq () (Nop ()) (Nop ())) (Seq () (Nop ()) (Nop ())),
                          0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' () (Fin () (Nop ())) (Evt () "z" (Seq () (EmitEvt () "z") (Nop ()))), 3, [], [], [])
        `shouldBe` (Par' () (Fin () (Nop ())) (Evt () "z" (Seq () (CanRun () 3) (Nop ()))), 4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Evt () "z" (Par' () (EmitEvt () "z") (AwaitEvt () "z")), 3, [], [], [])
        `shouldBe` (Evt () "z" (Par' () (CanRun () 3) (Nop ())), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' () (AwaitEvt () "d") (AwaitEvt () "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- pause --
  describe "(Pause () var p)" $ do
      it "pass: (Nop ())" $
        step (Var () ("x",Nothing) (Pause () "x" (Nop ())), 0, [], [], [])
        `shouldBe` (Var () ("x",Nothing) (Nop ()), 0, [], [], [])

      it "pass: awake" $
        step (Var () ("x",(Just 0)) (Pause () "x" (Evt () "e" (Par' () (AwaitEvt () "e") (EmitEvt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 0)) (Pause () "x" (Evt () "e" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "pass: awake - nested reaction inside Pause" $
        step (Var () ("x",(Just 1)) (Pause () "x" (Evt () "e" (Par' () (AwaitEvt () "e") (EmitEvt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 1)) (Pause () "x" (Evt () "e" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "pass: don't awake - nested reaction outside Pause" $
        step (Var () ("x",(Just 1)) (Evt () "e" (Pause () "x" (Par' () (AwaitEvt () "e") (EmitEvt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 1)) (Evt () "e" (Pause () "x" (Par' () (AwaitEvt () "e") (CanRun () 0)))),1,[],[],[])

      it "pass: awake - nested reaction outside Pause" $
        step (Var () ("x",(Just 0)) (Evt () "e" (Pause () "x" (Par' () (AwaitEvt () "e") (EmitEvt () "e")))), 0, [], [], [])
        `shouldBe` (Var () ("x",(Just 0)) (Evt () "e" (Pause () "x" (Par' () (Nop ()) (CanRun () 0)))),1,[],[],[])

      it "fail: undeclared var" $
        forceEval (step (Evt () "e" (Pause () "x" (EmitEvt () "e")), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninit var" $
        forceEval (step (Evt () "e" (Var () ("x",Nothing) (Pause () "x" (EmitEvt () "e"))), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (program is blocked)" $ do

      stepsItPass
        (AwaitInp () "A", 0, [], [], [])
        (AwaitInp () "A", 0, [], [], [])

      stepsItPass
        (AwaitEvt () "a", 0, [], [], [])
        (AwaitEvt () "a", 0, [], [], [])

      stepsItPass
        (Seq () (AwaitEvt () "a") (Nop ()), 0, [], [], [])
        (Seq () (AwaitEvt () "a") (Nop ()), 0, [], [], [])

      stepsItPass
        (Every () "A" (Nop ()), 0, [], [], [])
        (Every () "A" (Nop ()), 0, [], [], [])

      stepsItPass
        (Pause () "a" (AwaitInp () ""), 0, [], [], [])
        (Pause () "a" (AwaitInp () ""), 0, [], [], [])

      stepsItPass
        (Fin () (Seq () (Nop ()) (Nop ())), 0, [], [], [])
        (Fin () (Seq () (Nop ()) (Nop ())), 0, [], [], [])

      stepsItPass
        (Par' () (AwaitInp () "A") (Fin () (Nop ())), 0, [], [], [])
        (Par' () (AwaitInp () "A") (Fin () (Nop ())), 0, [], [], [])

      stepsItPass
        (Par' () (AwaitInp () "A") (Fin () (Nop ())), 0, [], [], [])
        (Par' () (AwaitInp () "A") (Fin () (Nop ())), 0, [], [], [])

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
        (Evt () "z" (EmitEvt () "z"), 3, [], [], [])
        ((Nop ()), 0, [], [], [])
        --(Evt () "z" (CanRun () 3), 4, [], [], [])

      stepsItPass
        (CanRun () 3, 3, [], [], [])
        ((Nop ()), 0, [], [], [])

      stepsItPass
        ((Nop ()) `sSeq` (Nop ()) `sSeq` (Nop ()) `sSeq` (Escape () 0) `sSeq` (Nop ()), 0, [], [], [])
        ((Escape () 0), 0, [], [], [])

      stepsItPass
        (Loop' () (Escape () 0) (Escape () 0) `sSeq` (Nop ()) `sSeq` (Nop ()) `sSeq` (Evt () "z" (EmitEvt () "z")) `sSeq` (Escape () 0),
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
        ((Seq () (Evt () "z" (EmitEvt () "z")) (Nop ())), 3, [], [], [])
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
        isBlocked 3 (Par' () (Nop ()) (Seq () (CanRun () 3) (Seq () (Evt () "z" (EmitEvt () "z")) (Nop ()))))
        `shouldBe` False

      stepsItPass
        ((Seq () (Trap () (Loop' () (Escape () 0) (Escape () 0))) (Nop ())) `sPar` (Seq () (Evt () "z" (EmitEvt () "z")) (Nop ())), 3, [], [], [])
        (Par' () (Nop ()) (Nop ()),0,[],[],[])

      stepsItPass
        (Seq () (Trap () (Trap () (Loop' () (Escape () 1) (Escape () 1)))) (Nop ()) `sPar` Seq () (Evt () "z" (EmitEvt () "z")) (Nop ()), 3, [], [], [])
        (Par' () (Nop ()) (Nop ()),0,[],[],[])

      stepsItPass
        (Trap () (Loop' ()
          (((Nop ()) `sSeq` (AwaitEvt () "d")) `sPar`
            ((AwaitInp () "M") `sPar` ((Nop ()) `sSeq` (Escape () 0))))
          (((Nop ()) `sSeq` (AwaitEvt () "d")) `sPar`
            ((AwaitInp () "M") `sPar` ((Nop ()) `sSeq` (Escape () 0))))), 0, [], [], [])
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
        out1 (Seq () (AwaitEvt () "b") Break, 3, Just "b", [], [])
        `shouldBe` (Seq () (Nop ()) Break, 4, [], [], [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq () (AwaitEvt () "c") Break, 3, Just "b", [], [])
        `shouldBe` (Seq () (AwaitEvt () "c") Break, 4, [], [], [])

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
        let d = (Evt () "x" (EmitEvt () "x"), 0, [], [], [])
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
        let d = (bcast "c" [] (AwaitEvt () "d"), 0, [], [], [])
            d' = (AwaitEvt () "d", 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl > 0, but `(Nop ())`" $
        let d = (bcast "d" [] (AwaitEvt () "d"), 88, [], [], [])
            d' = ((Nop ()), 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      (Evt () "d"
        (Par ()
          (EmitEvt () "d")
          (((Nop ()) `sSeq` AwaitEvt () "d") `sPar` ((Nop ()) `sSeq` Fin () (Nop ()))
      )), "_", [])
      (Evt () "d" (Par' () (Nop ()) (Par' () (AwaitEvt () "d") (Fin () (Nop ())))),[],[])

    reactionItPass
      (Evt () "d" (((Nop ()) `sSeq` AwaitEvt () "d") `sPar` ((Nop ()) `sSeq` EmitEvt () "d")), "_", [])
      (Evt () "d" (Par' () (Nop ()) (Nop ())),[],[])

    reactionItPass
      (Var () ("x",(Just 0)) (Evt () "e" (Pause () "x" (Trap () (Par () (Seq () (AwaitEvt () "e") (Escape () 0)) (EmitEvt () "e"))))), "_", [])
      ((Nop ()), [], [])

    reactionItPass
      (Var () ("x",(Just 1)) (Evt () "e" (Pause () "x" (Trap () (Par () (Seq () (AwaitEvt () "e") (Escape () 0)) (EmitEvt () "e"))))), "_", [])
      (Var () ("x",Just 1) (Evt () "e" (Pause () "x" (Trap () (Par' () (Seq () (AwaitEvt () "e") (Escape () 0)) (Nop ()))))),[],[])

  --------------------------------------------------------------------------
  describe "compile_run" $ do

    evalProgItSuccess (11,[[]])
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 10)])) `G.sSeq`
            G.Escape () 0)))

    evalProgItFail ["escape: orphan `escape` statement","trap: missing `escape` statement","halt: unreachable statement"]
      [] (G.Escape () 1)

    evalProgItFail ["declaration: identifier '_ret' is already declared"]
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Var () "_ret" (Type1 "Int")
             (G.Write () "a" (Const () 1) `G.sSeq`
              G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"), (Const () 10)])) `G.sSeq`
              G.Escape () 0))))

    evalProgItFail ["declaration: identifier '_ret' is already declared"]
      [] (G.Write () "_ret" (Const () 1) `G.sSeq`
          G.Var () "_ret" (Type1 "Int") (G.Write () "_ret" (Const () 99)) `G.sSeq`
          G.Escape () 0)

    evalProgItSuccess (11,[[]])
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Var () "b" (Type1 "Int") (G.Write () "b" (Const () 99)) `G.sSeq`
            G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 10)])) `G.sSeq`
            G.Escape () 0)))

    evalProgItFail ["declaration: identifier 'a' is already declared"]
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Var () "a" (Type1 "Int") (G.Write () "a" (Const () 99)) `G.sSeq`
            G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 10)])) `G.sSeq`
            G.Escape () 0)))

    evalProgItSuccess (2,[[]])
      [] (G.Write () "_ret" (Const () 1) `G.sSeq`
          G.Var () "_" (Type1 "Int") (G.Write () "_ret" (Const () 2)) `G.sSeq`
          G.Escape () 0)

    evalProgItSuccess (12,[[]])
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Trap () (G.Par ()
             (G.Var () "b" (Type1 "Int") (G.Write () "b" (Const () 99) `G.sSeq` G.Inp () "A" (G.AwaitInp () "A")) `G.sSeq` (G.Halt ()))
             (G.Escape () 0)) `G.sSeq`
           G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 11)])) `G.sSeq`
           G.Escape () 0)))

    evalProgItFail ["trap: missing `escape` statement"]
      [] (G.Trap () (G.Par ()
           (G.Inp () "A" (G.Var () "x" (Type1 "Int") (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ())))
           (G.Escape () 1)))

    evalProgItSuccess (1,[[]])
      [] (G.Seq () (G.Trap () (G.Inp () "A" (G.Par ()
           (G.Var () "x" (Type1 "Int") (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ()))
           (G.Escape () 0)))) (G.Escape () 0))

    evalProgItFail ["loop: `loop` never iterates","declaration: identifier 'a' is already declared"]
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Trap () (G.Inp () "A" (G.Loop () (G.Par ()
                  (G.Var () "a" (Type1 "Int") (G.Write () "a" (Const () 99) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ()))
                  (G.Escape () 0)))) `G.sSeq`
             G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 10)])) `G.sSeq`
            G.Escape () 0)))

    evalProgItSuccess (101,[[]])
      [] (G.CodI () "add" (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int") (G.Var () "a" (Type1 "Int")
           (G.Write () "a" (Const () 1) `G.sSeq`
            G.Inp () "A" (G.Trap () (G.Par ()
                  (G.Var () "b" (Type1 "Int") (G.Write () "b" (Const () 99) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ()))
                  (G.Escape () 0)) `G.sSeq`
            G.Write () "_ret" (Call () "add" (Tuple () [(Read () "a"),(Const () 100)])) `G.sSeq`
            G.Escape () 0))))

    evalProgItFail ["loop: `loop` never iterates"]
      [] (G.Seq () (G.Trap () (G.Loop () (G.Par ()
                 (G.Inp () "A" (G.Var () "x" (Type1 "Int") (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ())))
                 (G.Escape () 0)))) (G.Escape () 0))

    evalProgItSuccess (1,[[]])
      [] (G.Seq () (G.Trap () (G.Par ()
                 (G.Inp () "A" (G.Var () "x" (Type1 "Int") (G.Write () "_ret" (Const () 1) `G.sSeq` G.AwaitInp () "A" `G.sSeq` G.Halt ())))
                 (G.Escape () 0))) (G.Escape () 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write () "_ret" (Const () 1)) `G.sSeq`
      (G.Evt () "a"
        (G.Trap ()
        (G.Par ()
          ((G.AwaitEvt () "a") `G.sSeq` (G.Write () "_ret" (Const () 5)) `G.sSeq` (G.Escape () 0))
          ((G.EmitEvt () "a") `G.sSeq` G.Halt ())))) `G.sSeq`
      (G.Escape () 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write () "_ret" (Const () 1)) `G.sSeq`
      (G.Evt () "a"
        (G.Trap () (G.Par ()
          ((G.AwaitEvt () "a") `G.sSeq` (G.Write () "_ret" (Const () 5)) `G.sSeq` (G.Escape () 0))
          (G.Seq () (G.Trap () (G.Par () (G.Fin () (G.EmitEvt () "a")) (G.Escape () 0))) (G.Escape () 0)))
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
      (G.Var () "x" (Type1 "Int") (
        (G.Write () "x" (Const () 10)) `G.sSeq`
        (G.Trap () (G.Par ()
          (G.Var () "y" (Type1 "Int") (G.Halt ()))
          (G.Seq () (G.Write () "x" (Const () 99)) (G.Escape () 0))
        )) `G.sSeq`
        (G.Write () "_ret" (Read () "x")) `G.sSeq`
        (G.Escape () 0)
      )))

    evalProgItSuccess (99,[[],[]]) ["A"]
      (G.Seq () (G.Seq ()
        (G.Var () "x" (Type1 "Int")
          (G.Seq ()
            (G.Write () "x" (Const () 1))
            (G.Evt () "e"
              (G.Trap () (G.Par ()
                (G.Inp () "A" (G.Seq () (G.AwaitInp () "A") (G.Seq () (G.Write () "x" (Const () 0)) (G.Seq () (G.EmitEvt () "e") (G.Halt ())))))
                (G.Seq () (G.Pause () "x" (G.Trap () (G.Par () (G.Seq () (G.AwaitEvt () "e") (G.Escape () 0)) ((G.EmitEvt () "e") `G.sSeq` (G.Halt ()))))) (G.Escape () 0)))))))
        (G.Write () "_ret" (Const () 99))) (G.Escape () 0))

    -- multiple inputs

    evalProgItSuccess (1,[[],[]])
      ["A"] (G.Inp () "A" (G.AwaitInp () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` (G.Escape () 0)))

    evalProgItFail ["program didn't terminate"]
      [] (G.Inp () "A" (G.AwaitInp () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0))

    evalProgItFail ["program didn't terminate"]
      ["B"] (G.Inp () "A" (G.AwaitInp () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0))

    evalProgItFail ["pending inputs"]
      ["A","A"] (G.Inp () "A" (G.AwaitInp () "A" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0))

    evalProgItSuccess (1,[[],[],[]])
      ["A","B"] (G.Inp () "A" (G.Inp () "B" (G.AwaitInp () "A" `G.sSeq` G.AwaitInp () "B" `G.sSeq` G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)))

    evalProgItSuccess (1,[[]]) [] (G.Write () "_ret" (Const () 1) `G.sSeq` G.Escape () 0)

    -- multiple outputs

    describe "out:" $ do
        it "out O; emit O" $
            compile_run (G.Out () "O" (G.Seq () (G.EmitExt () "O" Nothing) (G.Seq () (G.Write () "_ret" (Const () 1)) (G.Escape () 0))))
                []
            `shouldBe` Right (1,[[("O",Nothing)]])

        it "I-F-O" $
            compile_run (G.Out () "O" (G.Inp () "I" (G.Inp () "F" (G.Seq () (G.Seq () (G.Write () "_ret" (Const () 1)) (G.Trap () (G.Par () (G.Seq () (G.AwaitInp () "F") (G.Escape () 0)) (G.Every () "I" (G.EmitExt () "O" Nothing))))) (G.Escape () 0)))))
                ["I","I","F"]
            `shouldBe` Right (1,[[],[("O",Nothing)],[("O",Nothing)],[]])

      where
        stepsItPass (p,n,e,vars,outs) (p',n',e',vars',outs') =
          (it (printf "pass: %s -> %s#" (show p) (show p'))
           ((steps (p,n,e,vars,outs) `shouldBe` (p',n',e',vars',outs'))
             >> ((isReducible (p',n',e',vars',outs')) `shouldBe` False)))

        stepsItFail err (p,n,e,vars,outs) =
          (it (printf "fail: %s ***%s" (show p) err)
           (forceEval (steps (p,n,e,vars,outs)) `shouldThrow` errorCall err))

        reactionItPass (p,e,vars) (p',vars',outs') =
          (it (printf "pass: %s | %s -> %s" e (show p) (show p'))
            (reaction p e `shouldBe` (p',outs')))

        evalProgItSuccess (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (show prog) res (show outss)) $
            (compile_run prog hist `shouldBe` Right (res,outss)))

        evalProgItFail err hist prog =
          (it (printf "pass: %s | %s ***%s" (show hist) (show prog) (show err)) $
            (compile_run prog hist `shouldBe` Left err))
