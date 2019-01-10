module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Ann      (annz)
import Ceu.Grammar.Exp      (Exp(..))
import qualified Ceu.Grammar.Stmt as G
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

-- Declare Exp, Stmt, and Desc as datatypes that can be fully evaluated.
instance NFData Exp where
  rnf (RawE  _ _)   = ()
  rnf (Const _ _)   = ()
  rnf (Read  _ _)   = ()
  rnf (Unit  _)     = ()
  rnf (Tuple _ _)   = ()
  rnf (Call  _ _ _) = ()

instance NFData Stmt where
  rnf (Write _ expr) = rnf expr
  rnf (AwaitInp _)   = ()
  rnf (AwaitEvt _)   = ()
  rnf (EmitEvt _)    = ()
  rnf (If expr p q)  = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq p q)      = rnf p `deepseq` rnf q
  rnf (Every _ p)    = rnf p
  rnf (Par p q)      = rnf p `deepseq` rnf q
  rnf (Pause _ p)    = rnf p
  rnf (Fin p)        = rnf p
  rnf (Trap p)       = rnf p
  rnf (Escape _)     = ()
  rnf (Nop)          = ()
  rnf (Error _)      = ()
  rnf (CanRun _)     = ()
  rnf (Var _ p)      = rnf p
  rnf (Evt _ p)      = rnf p
  rnf (Loop' p q)    = rnf p
  rnf (Par' p q)     = rnf p `deepseq` rnf q

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
      it "pass: vars == [] && exp == (Const _)" $
        varsEval [] (Const annz 0) `shouldBe` 0

      it "fail: undeclared variable" $
        forceEval (varsEval [] (Read annz "x"))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninitialized variable" $
        forceEval (varsEval [("x",Nothing)] (Read annz "x"))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

      it "pass: eval in simple env" $
        let vars = [("x",Just 1),("y",Just 2)] in
          varsEval vars (Call annz "(+)" (Tuple annz [(Call annz "(-)" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let vars = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval vars (Call annz "(+)" (Tuple annz [(Call annz "(-)" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
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
        `shouldBe` (Var ("x",Nothing) Nop, 0, [], [], [])

      it "pass: Var [\"x\"] p" $
        step (Var "x" (Seq Nop Nop), 0, [], [], [])
        `shouldBe` (Var ("x",Nothing) (Seq Nop Nop)), 0, [], [], [])
-}

    -- write --
    describe "(Write id exp)" $ do
      it "fail: [] x=y (undeclared variable)" $
        (forceEval $ step (Write "x" (Read annz "y"), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "fail: [] x=1 (undeclared variable)" $
        (forceEval $ step (Write "x" (Const annz 1), 0, [], [], []))
        `shouldThrow` errorCall "varsWrite: undeclared variable: x"

      it "pass: [x=?] x=1" $
        step (Var ("x",Nothing) (Write "x" (Const annz 1)), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 1)) Nop, 0, [], [], [])

      it "pass: [x=1] x=2" $
        step (Var ("x",(Just 1)) (Write "x" (Const annz 2)), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 2)) Nop, 0, [], [], [])

      -- TODO: test is correct but fails
      it "fail: [x=1,y=?] x=y (uninitialized variable) | TODO: ok" $
        let p = Var ("x",(Just 1))
               (Var ("y",Nothing)
                 (Write "x" (Read annz "y"))) in
          (forceEval $ step (p, 0, [], [], []))
          `shouldThrow` errorCall "varsRead: uninitialized variable: y"

      it "fail: TODO: ok" $
        (forceEval $ step (EmitEvt "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "fail: TODO: ok" $
        (forceEval $ step (Var ("_ret",Nothing) ((Write "_ret" (Const annz 25)) `Seq` (EmitEvt "a")), 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Write "x" (Const annz 1))), 0, [], [], [])
        `shouldBe`
        (Var ("x",Nothing)
          (Write "x" (Const annz 1)), 0, [], [], [])

      it "pass: [x=1,y=?] y=x+2" $
        step (
          (Var ("x",(Just 1))
          (Var ("y",Nothing)
            (Write "y" (Call annz "(+)" (Tuple annz [(Read annz "x"),(Const annz 2)])))), 0, [], [], []))
        `shouldBe` (Var ("x",(Just 1)) (Var ("y",(Just 3)) Nop),0,[],[], [])

      it "pass: [x=1,y=?] y=x+2" $
        step
        (Var ("x",(Just 1))
        (Var ("y",Nothing)
          (Write "y" (Call annz "(+)" (Tuple annz [(Read annz "x"),(Const annz 2)])))), 0, [], [], [])
        `shouldBe`
        (Var ("x",(Just 1))
        (Var ("y",(Just 3)) Nop), 0, [], [], [])

      it "pass: [x=?] x=-(5+1)" $
        step
        (Var ("x",(Just 0))
          (Write "x" (Call annz "negate" (Call annz "(+)" (Tuple annz [(Const annz 5),(Const annz 1)])))), 0, [], [], [])
        `shouldBe`
        (Var ("x",(Just (-6))) Nop, 0, [], [], [])

    -- emit-int --
  describe "(EmitEvt e')" $ do
      it "fail: {? emit a}" $
        forceEval (step (EmitEvt "a", 0, [], [], []))
        `shouldThrow` errorCall "evtsEmit: undeclared event: a"

      it "pass: lvl == 0" $
        step (Evt "a" (EmitEvt "a"), 0, [], [], [])
        `shouldBe` (Evt "a" (CanRun 0), 1, [], [], [])

      it "pass: pop" $
        (step (Evt "a" (CanRun 0), 1, [], [], []))
        `shouldBe` (Evt "a" (CanRun 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Evt "b" (EmitEvt "b"), 3, [], [], [])
        `shouldBe` (Evt "b" (CanRun 3), 4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (EmitEvt "b", 3, Just "b", [], []))
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
        step (Seq Nop (Escape 0), 3, [], [], [])
        `shouldBe` ((Escape 0), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Seq Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- seq-brk --
  describe "(Seq (Escape k) q)" $ do
      it "pass: lvl == 0" $
        step (Seq (Escape 0) Nop, 0, [], [], [])
        `shouldBe` ((Escape 0), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Seq (Escape 0) (EmitEvt "z"), 3, [], [], [])
        `shouldBe` ((Escape 0), 3, [], [], [])

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
        step (Seq (Seq (Evt "z" (EmitEvt "z")) Nop) Nop, 3, [], [], [])
        `shouldBe` (Seq (Seq (Evt "z" (CanRun 3)) Nop) Nop, 4, [], [], [])

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
        forceEval (step (If (Read annz "x") Nop (Escape 0), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "pass: x == 0" $
        step (If (Read annz "x") Nop (Escape 0), 0, [("x",Just 0)], [], [])
        `shouldBe` ((Escape 0), 0, [("x",Just 0)], [], [])

      it "pass: x /= 0" $
        step (If (Read annz "x") Nop (Escape 0), 0, [("x",Just 1)], [], [])
        `shouldBe` (Nop, 0, [("x",Just 1)], [], [])

{-
  -- loop-expd --
  describe "(Loop p)" $ do
      it "pass: lvl == 0" $
        step (Loop Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop (Seq Nop (EmitEvt "z")), 3, [], [], [])
        `shouldBe`
        (Loop' (Seq Nop (EmitEvt "z")) (Seq Nop (EmitEvt "z")), 3, [], [], [])

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
        step (Loop' Nop (EmitEvt "z"), 3, [], [], [])
        `shouldBe` (Loop' (EmitEvt "z") (EmitEvt "z"), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Loop' (Fin Nop) (Fin Nop), 0, [], [], [])

  -- loop-brk --
  describe "(Loop' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Escape 0) Nop, 0, [], [], [])
        `shouldBe` (Escape 0, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' (Escape 0) (Seq (EmitEvt "z") Nop), 3, [], [], [])
        `shouldBe` ((Escape 0), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Loop' Break Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        step (Loop' (Escape 0) (Fin Nop), 0, [], [], [])
        `shouldBe` ((Escape 0), 0, [], [], [])

  -- loop-adv --
  describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Seq Nop Nop) Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Evt "z" (Loop' (Seq (EmitEvt "z") Nop) (Escape 0)), 3, [], [], [])
        `shouldBe` (Evt "z" (Loop' (Seq (CanRun 3) Nop) (Escape 0)), 4, [], [], [])

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

  -- par-expd --
  describe "(Par p q)" $ do
      it "pass: lvl == 0" $
        step (Par Nop Nop, 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (CanRun 0) Nop), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Par (Nop `Seq` EmitEvt "z")  (Nop `Seq` Nop),
               3, [], [], [])
        `shouldBe` (Par' (Nop `Seq` EmitEvt "z")
                            (CanRun 3 `Seq` (Nop `Seq` Nop)), 3, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (And Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par (Fin Nop) Nop, 0, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Seq (CanRun 0) Nop),
                     0, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Par Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (CanRun 0) (Fin Nop)),
                    0,[],[],[])

      it "pass: isBlocked p && isBlocked q" $
        step (Par (Fin Nop) (Fin Nop), 0, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
                    0,[],[],[])

  -- par-nop1 --
  describe "(Par' Nop q)" $ do
      it "fail: Par does not advance on Nops" $
        forceEval (step (Par' Nop Nop, 0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

{-
      it "pass: lvl > 0" $
        step (Par' Nop (EmitEvt "z"), 3, [], [], [])
        `shouldBe` (Par' Nop (EmitEvt "z"), 2, [], [], [])

      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        forceEval (step (Par' Nop (Fin Nop), 0, [], [], []))
        --`shouldBe` (Fin Nop, 0, [], [], [])
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: q == Nop" $
        forceEval (step (Par' Nop Nop, 0, [], [], []))
        --`shouldBe` (Nop, 0, [], [], [])
        `shouldThrow` errorCall "step: cannot advance"

      it "pass: q == (Escape 0)" $
        step (Par' Halt (Escape 0), 0, [], [], [])
        `shouldBe` ((Seq Nop (Escape 0)), 0, [], [], [])

  -- par-brk1 --
  describe "(Par' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitInp "A") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
            `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitEvt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 3, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Escape 0) (Var ("_",Nothing) Nop), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
            `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' (AwaitInp "A" `Seq` Fin Nop)
                    (Par' (Fin (EmitEvt "b"))
                          (Par' (Fin (EmitEvt "c" `Seq` EmitEvt "d"))
                            (AwaitEvt "a" `Seq` Fin (EmitEvt "e"))))
            clear_q = Nop `Seq` EmitEvt "b" `Seq`
                      (EmitEvt "c" `Seq` EmitEvt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
            `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: clear Par'" $
        (step (Par' (Escape 0) Nop, 0, [], [], []))
        `shouldBe` (Seq Nop (Escape 0), 0, [], [], [])

      it "fail: q == (Escape 0) (invalid clear)" $
        forceEval (step (Par' (Escape 0) (Escape 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- par-nop2 --
  describe "(Par' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        step (Par' (Fin Nop) Halt, 1, [], [], [])
        `shouldBe` (Par' (Fin Nop) Halt,0,[],[],[])

      it "pass: lvl > 0 && isBlocked p" $
        step (Par' (Seq (Fin Nop) Nop) Halt, 3, [], [], [])
        `shouldBe` (Par' (Seq (Fin Nop) Nop) Halt,2,[],[],[])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Fin Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: p == Nop" $
        step (Par' Halt Halt, 1, [], [], [])
        `shouldBe` (Par' Halt Halt,0,[],[],[])

  -- par-brk2 --
  describe "(Par' p (Escape 0))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitEvt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Par' p (Escape 0), 0, [], [], [])
           `shouldBe` (Seq (clear p) (Escape 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` (Seq Nop Nop))
          >>
          (step (Par' p (Escape 0), 3, [], [], [])
           `shouldBe` (Seq (clear p) (Escape 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Fin Nop) (Escape 0), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Par' (AwaitInp "A" `Seq` Fin Nop)
                    (Par' (Fin (EmitEvt "b"))
                          (Par' (Fin (EmitEvt "c" `Seq` EmitEvt "d"))
                            (AwaitEvt "a" `Seq` Fin (EmitEvt "e"))))
            clear_p = Nop `Seq` EmitEvt "b" `Seq`
                      (EmitEvt "c" `Seq` EmitEvt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Par' p (Escape 0), 0, [], [], [])
            `shouldBe` (Seq (clear p) (Escape 0), 0, [], [], []))

      it "pass: p == Nop" $
        step (Par' Halt (Escape 0), 0, [], [], [])
        `shouldBe` (Seq Nop (Escape 0), 0, [], [], [])

      it "fail: p == (Escape 0) (invalid clear)" $
        forceEval (step (Par' (Escape 0) (Escape 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- par-adv --
  describe "(Par' p q)" $ do
      it "pass: lvl == 0" $
        step (Par' (Seq Nop Nop) (Seq (Escape 0) (Escape 0)), 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (Escape 0) (Escape 0)), 0, [], [], [])

      it "pass: lvl > 0" $
        step (Evt "y" (Evt "z" (Par' (Seq (EmitEvt "z") Nop) (Seq (EmitEvt "y") Nop))),
               3, [], [], [])
        `shouldBe` (Evt "y" (Evt "z" (Par' (Seq (CanRun 3) Nop) (Seq (EmitEvt "y") Nop))),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Seq Nop Nop) (Seq Nop Nop),
                         0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' (Fin Nop) (Seq (Evt "z" (EmitEvt "z")) Nop),
               3, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Seq (Evt "z" (CanRun 3)) Nop),
                     4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Evt "z" (Par' (EmitEvt "z") (AwaitEvt "z")), 3, [], [], [])
        `shouldBe` (Evt "z" (Par' (CanRun 3) Nop), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' (AwaitEvt "d") (AwaitEvt "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- par-expd --
  describe "(Par p q)" $ do
      it "pass: lvl == 0" $
        step (Par Nop Nop, 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (CanRun 0) Nop),
                    0,[],[],[])

      it "pass: lvl > 0" $
        step (Par (Seq Nop (EmitEvt "z")) (Seq Nop Nop), 3, [], [], [])
        `shouldBe` (Par' (Seq Nop (EmitEvt "z")) (Seq (CanRun 3) (Seq Nop Nop)),
                    3,[],[],[])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par (Fin Nop) Nop, 0, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Seq (CanRun 0) Nop),
                    0,[],[],[])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Par Nop (Fin Nop), 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (CanRun 0) (Fin Nop)),
                    0,[],[],[])

      it "pass: isBlocked p && isBlocked q" $
        step (Par (Fin Nop) (Fin Nop), 0, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Seq (CanRun 0) (Fin Nop)),
                    0,[],[],[])

  -- or-nop1 --
  describe "(Par' Nop q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitEvt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: lvl > 0" $
        let q = (AwaitEvt "z") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 1) q, 3, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 1), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Or' Nop Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = (Fin Nop) in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' (AwaitInp "A" `Seq` Fin Nop)
                    (Par' (Fin (EmitEvt "b"))
                          (Par' (Fin (EmitEvt "c" `Seq` EmitEvt "d"))
                            (AwaitEvt "a" `Seq` Fin (EmitEvt "e"))))
            clear_q = Nop `Seq` EmitEvt "b" `Seq`
                      (EmitEvt "c" `Seq` EmitEvt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
            `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

  -- or-brk1 --
  describe "(Par' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        let q = (AwaitEvt "a") in
          (clear q `shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "transit: lvl > 0" $
        let q = (AwaitEvt "z") in
          (clear q`shouldBe` Nop)
          >>                    -- clear q == Nop
          (step (Par' (Escape 0) q, 3, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Escape 0) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked q" $
        let q = Fin (Seq Nop Nop) in
          (clear q `shouldBe` (Seq Nop Nop))
          >>                    -- clear q == Nop; Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
           `shouldBe` (Seq (clear q) (Escape 0), 0, [], [], []))

      it "pass: isBlocked q (nontrivial clear)" $
        let q = Par' (AwaitInp "A" `Seq` Fin Nop)
                    (Par' (Fin (EmitEvt "b"))
                          (Par' (Fin (EmitEvt "c" `Seq` EmitEvt "d"))
                            (AwaitEvt "a" `Seq` Fin (EmitEvt "e"))))
            clear_q = Nop `Seq` EmitEvt "b" `Seq`
                      (EmitEvt "c" `Seq` EmitEvt "d") `Seq` Nop in
          (clear q `shouldBe` clear_q)
          >>                   -- clear q == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Par' (Escape 0) q, 0, [], [], [])
            `shouldBe` (Seq clear_q (Escape 0), 0, [], [], []))

  -- or-nop2 --
  describe "(Par' p Nop)" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (Fin Nop) in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Par' p (Escape 0), 0, [], [], [])
            `shouldBe` (Seq (clear p) (Escape 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Seq (Fin Nop) Nop in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Par' p (Escape 0), 3, [], [], [])
            `shouldBe` (Seq (clear p) (Escape 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Fin Nop) Nop, 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

  -- or-brk2 --
  describe "(Par' p (Escape 0))" $ do
      it "pass: lvl == 0 && isBlocked p" $
        let p = (AwaitEvt "b") in
          (clear p `shouldBe` Nop)
          >>                    -- clear p == Nop
          (step (Par' p (Escape 0), 0, [], [], [])
           `shouldBe` (Seq (clear p) (Escape 0), 0, [], [], []))

      it "pass: lvl > 0 && isBlocked p" $
        let p = Fin (Seq Nop Nop) in
          (clear p `shouldBe` Seq Nop Nop)
          >>                    -- clear p == Nop; Nop
          (step (Par' p (Escape 0), 3, [], [], [])
            `shouldBe` (Seq (clear p) (Escape 0), 3, [], [], []))

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Fin Nop) (Escape 0), 0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p (nontrivial clear)" $
        let p = Par' (AwaitInp "A" `Seq` Fin Nop)
                    (Par' (Fin (EmitEvt "b"))
                          (Par' (Fin (EmitEvt "c" `Seq` EmitEvt "d"))
                            (AwaitEvt "a" `Seq` Fin (EmitEvt "e"))))
            clear_p = Nop `Seq` EmitEvt "b" `Seq`
                      (EmitEvt "c" `Seq` EmitEvt "d") `Seq` Nop in
          (clear p `shouldBe` clear_p)
          >>                   -- clear p == Nop; Emit1; (Emit2; Emit3); Nop
          (step (Par' p (Escape 0), 0, [], [], [])
            `shouldBe` (Seq (clear p) (Escape 0), 0, [], [], []))

      it "fail: p == Nop (invalid clear)" $
        (step (Par' Halt (Escape 0), 0, [], [], []))
        `shouldBe` (Seq Nop (Escape 0),0,[],[],[])

      it "fail: p == (Escape 0) (invalid clear)" $
        forceEval (step (Par' (Escape 0) (Escape 0), 0, [], [], []))
        `shouldThrow` errorCall "clear: invalid clear"

  -- or-adv --
  describe "(Par' p q)" $ do
      it "pass: lvl == 0" $
        step (Par' (Seq Nop Nop) (Seq (Escape 0) (Escape 0)), 0, [], [], [])
        `shouldBe` (Par' Nop (Seq (Escape 0) (Escape 0)), 0, [], [], [])

      it "psas: lvl > 0" $
        step (Par' (Evt "z" (Seq (EmitEvt "z") Nop)) (Evt "y" (Seq (EmitEvt "y") Nop)),
               3, [], [], [])
        `shouldBe` (Par' (Evt "z" (Seq (CanRun 3) Nop)) (Evt "y" (Seq (EmitEvt "y") Nop)),
                     4, [], [], [])

{-
      it "fail: evt /= nil (cannot advance)" $
        forceEval (step (Par' (Seq Nop Nop) (Seq Nop Nop),
                          0, Just "b", [], []))
        `shouldThrow` errorCall "step: cannot advance"
-}

      it "pass: isBlocked p && not (isBlocked q)" $
        step (Par' (Fin Nop) (Evt "z" (Seq (EmitEvt "z") Nop)), 3, [], [], [])
        `shouldBe` (Par' (Fin Nop) (Evt "z" (Seq (CanRun 3) Nop)), 4, [], [], [])

      it "pass: not (isBlocked p) && isBlocked q" $
        step (Evt "z" (Par' (EmitEvt "z") (AwaitEvt "z")), 3, [], [], [])
        `shouldBe` (Evt "z" (Par' (CanRun 3) Nop), 4, [], [], [])

      it "fail: isBlocked p && isBlocked q (cannot advance)" $
        forceEval (step (Par' (AwaitEvt "d") (AwaitEvt "e"),
                          0, [], [], []))
        `shouldThrow` errorCall "step: cannot advance"

  -- pause --
  describe "(Pause var p)" $ do
      it "pass: Nop" $
        step (Var ("x",Nothing) (Pause "x" Nop), 0, [], [], [])
        `shouldBe` (Var ("x",Nothing) Nop, 0, [], [], [])

      it "pass: awake" $
        step (Var ("x",(Just 0)) (Pause "x" (Evt "e" (Par' (AwaitEvt "e") (EmitEvt "e")))), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 0)) (Pause "x" (Evt "e" (Par' Nop (CanRun 0)))),1,[],[],[])

      it "pass: awake - nested reaction inside Pause" $
        step (Var ("x",(Just 1)) (Pause "x" (Evt "e" (Par' (AwaitEvt "e") (EmitEvt "e")))), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 1)) (Pause "x" (Evt "e" (Par' Nop (CanRun 0)))),1,[],[],[])

      it "pass: don't awake - nested reaction outside Pause" $
        step (Var ("x",(Just 1)) (Evt "e" (Pause "x" (Par' (AwaitEvt "e") (EmitEvt "e")))), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 1)) (Evt "e" (Pause "x" (Par' (AwaitEvt "e") (CanRun 0)))),1,[],[],[])

      it "pass: awake - nested reaction outside Pause" $
        step (Var ("x",(Just 0)) (Evt "e" (Pause "x" (Par' (AwaitEvt "e") (EmitEvt "e")))), 0, [], [], [])
        `shouldBe` (Var ("x",(Just 0)) (Evt "e" (Pause "x" (Par' Nop (CanRun 0)))),1,[],[],[])

      it "fail: undeclared var" $
        forceEval (step (Evt "e" (Pause "x" (EmitEvt "e")), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "fail: uninit var" $
        forceEval (step (Evt "e" (Var ("x",Nothing) (Pause "x" (EmitEvt "e"))), 0, [], [], []))
        `shouldThrow` errorCall "varsRead: uninitialized variable: x"

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (program is blocked)" $ do

      stepsItPass
        (AwaitInp "A", 0, [], [], [])
        (AwaitInp "A", 0, [], [], [])

      stepsItPass
        (AwaitEvt "a", 0, [], [], [])
        (AwaitEvt "a", 0, [], [], [])

      stepsItPass
        (Seq (AwaitEvt "a") Nop, 0, [], [], [])
        (Seq (AwaitEvt "a") Nop, 0, [], [], [])

      stepsItPass
        (Every "A" Nop, 0, [], [], [])
        (Every "A" Nop, 0, [], [], [])

      stepsItPass
        (Pause "a" (AwaitInp ""), 0, [], [], [])
        (Pause "a" (AwaitInp ""), 0, [], [], [])

      stepsItPass
        (Fin (Seq Nop Nop), 0, [], [], [])
        (Fin (Seq Nop Nop), 0, [], [], [])

      stepsItPass
        (Par' (AwaitInp "A") (Fin Nop), 0, [], [], [])
        (Par' (AwaitInp "A") (Fin Nop), 0, [], [], [])

      stepsItPass
        (Par' (AwaitInp "A") (Fin Nop), 0, [], [], [])
        (Par' (AwaitInp "A") (Fin Nop), 0, [], [], [])

{-
      stepsItFail "step: cannot advance"
        (CanRun 5, 0, [], [], [])
-}

    describe "zero steps (no step-rule applies)" $ do

      stepsItPass
        (Nop, 0, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        ((Escape 0), 0, [], [], [])
        ((Escape 0), 0, [], [], [])

    describe "one+ steps" $ do

      stepsItPass
        (Var ("x",Nothing) (Write "x" (Const annz 0)), 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Evt "z" (EmitEvt "z"), 3, [], [], [])
        (Nop, 0, [], [], [])
        --(Evt "z" (CanRun 3), 4, [], [], [])

      stepsItPass
        (CanRun 3, 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        (Nop `Seq` Nop `Seq` Nop `Seq` (Escape 0) `Seq` Nop, 0, [], [], [])
        ((Escape 0), 0, [], [], [])

      stepsItPass
        (Loop' (Escape 0) (Escape 0) `Seq` Nop `Seq` Nop `Seq` (Evt "z" (EmitEvt "z")) `Seq` (Escape 0),
          3, [], [], [])
        ((Escape 0), 0, [], [], [])

      stepsItPass
        (Loop' (Escape 0) (Escape 0), 3, [], [], [])
        (Escape 0, 0, [], [], [])

      stepsItPass
        (Trap (Loop' (Escape 0) (Escape 0)), 3, [], [], [])
        (Nop, 0, [], [], [])

      stepsItPass
        ((Seq (Trap (Loop' (Escape 0) (Escape 0))) Nop), 3, [], [], [])
        (Nop,0,[],[],[])

      stepsItPass
        ((Seq (Evt "z" (EmitEvt "z")) Nop), 3, [], [], [])
        (Nop,0,[],[],[])

      it "nop par nop" $ do
        isBlocked 0 (Par' Nop Nop)
          `shouldBe` True
      it "nop par nop" $ do
        isReducible (Par' Nop Nop, 0, [], [], [])
          `shouldBe` False

      stepsItPass
        (Nop `Par` Nop, 3, [], [], [])
        (Par' Nop Nop,0,[],[],[])

      it "blocked/par" $ do
        isBlocked 3 (Par' Nop (Seq (CanRun 3) (Seq (Evt "z" (EmitEvt "z")) Nop)))
        `shouldBe` False

      stepsItPass
        ((Seq (Trap (Loop' (Escape 0) (Escape 0))) Nop) `Par` (Seq (Evt "z" (EmitEvt "z")) Nop), 3, [], [], [])
        (Par' Nop Nop,0,[],[],[])

      stepsItPass
        (Seq (Trap (Trap (Loop' (Escape 1) (Escape 1)))) Nop `Par` Seq (Evt "z" (EmitEvt "z")) Nop, 3, [], [], [])
        (Par' Nop Nop,0,[],[],[])

      stepsItPass
        (Trap (Loop'
          ((Nop `Seq` (AwaitEvt "d")) `Par`
            ((AwaitInp "M") `Par` (Nop `Seq` (Escape 0))))
          ((Nop `Seq` (AwaitEvt "d")) `Par`
            ((AwaitInp "M") `Par` (Nop `Seq` (Escape 0))))), 0, [], [], [])
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
        out1 (Seq (AwaitEvt "b") Break, 3, Just "b", [], [])
        `shouldBe` (Seq Nop Break, 4, [], [], [])

      it "pass: lvl > 0 && bcast fails" $
        out1 (Seq (AwaitEvt "c") Break, 3, Just "b", [], [])
        `shouldBe` (Seq (AwaitEvt "c") Break, 4, [], [], [])

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
        let d = (Evt "x" (EmitEvt "x"), 0, [], [], [])
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
        let d = (bcast "c" [] (AwaitEvt "d"), 0, [], [], [])
            d' = (AwaitEvt "d", 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

      it "pass: lvl > 0, but `Nop`" $
        let d = (bcast "d" [] (AwaitEvt "d"), 88, [], [], [])
            d' = (Nop, 0, [], [], []) in
          (steps d `shouldBe` d')
          >> (isReducible d' `shouldBe` False)
          -- >> (isReducible d' `shouldBe` True)

  --------------------------------------------------------------------------
  describe "reaction" $ do

    reactionItPass
      (Evt "d"
        (Par
          (EmitEvt "d")
          ((Nop `Seq` AwaitEvt "d") `Par` (Nop `Seq` Fin Nop)
      )), "_", [])
      (Evt "d" (Par' Nop (Par' (AwaitEvt "d") (Fin Nop))),[],[])

    reactionItPass
      (Evt "d" ((Nop `Seq` AwaitEvt "d") `Par` (Nop `Seq` EmitEvt "d")), "_", [])
      (Evt "d" (Par' Nop Nop),[],[])

    reactionItPass
      (Var ("x",(Just 0)) (Evt "e" (Pause "x" (Trap (Par (Seq (AwaitEvt "e") (Escape 0)) (EmitEvt "e"))))), "_", [])
      (Nop, [], [])

    reactionItPass
      (Var ("x",(Just 1)) (Evt "e" (Pause "x" (Trap (Par (Seq (AwaitEvt "e") (Escape 0)) (EmitEvt "e"))))), "_", [])
      (Var ("x",Just 1) (Evt "e" (Pause "x" (Trap (Par' (Seq (AwaitEvt "e") (Escape 0)) Nop)))),[],[])

  --------------------------------------------------------------------------
  describe "compile_run" $ do

    evalProgItSuccess (11,[[]])
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Escape annz 0)))

    evalProgItFail ["orphan `escape` statement","missing `escape` statement","unreachable statement"]
      [] (G.Escape annz 1)

    evalProgItSuccess (11,[[]])
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Var annz "b" (Type1 ["Int"]) (G.Write annz (LVar "b") (Const annz 99)) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Escape annz 0)))

    evalProgItFail ["identifier 'a' is already declared"]
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Var annz "a" (Type1 ["Int"]) (G.Write annz (LVar "a") (Const annz 99)) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Escape annz 0)))

    evalProgItSuccess (2,[[]])
      [] (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq`
          G.Var annz "_" (Type1 ["Int"]) (G.Write annz (LVar "_ret") (Const annz 2)) `G.sSeq`
          G.Escape annz 0)

    evalProgItSuccess (12,[[]])
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Trap annz (G.Par annz
             (G.Var annz "b" (Type1 ["Int"]) (G.Write annz (LVar "b") (Const annz 99) `G.sSeq` G.Inp annz "A" (G.AwaitInp annz "A")) `G.sSeq` (G.Halt annz))
             (G.Escape annz 0)) `G.sSeq`
           G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 11)])) `G.sSeq`
           G.Escape annz 0)))

    evalProgItFail ["missing `escape` statement"]
      [] (G.Trap annz (G.Par annz
           (G.Inp annz "A" (G.Var annz "x" (Type1 ["Int"]) (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz)))
           (G.Escape annz 1)))

    evalProgItSuccess (1,[[]])
      [] (G.Seq annz (G.Trap annz (G.Inp annz "A" (G.Par annz
           (G.Var annz "x" (Type1 ["Int"]) (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz))
           (G.Escape annz 0)))) (G.Escape annz 0))

    evalProgItFail ["`loop` never iterates","identifier 'a' is already declared"]
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Trap annz (G.Inp annz "A" (G.Loop annz (G.Par annz
                  (G.Var annz "a" (Type1 ["Int"]) (G.Write annz (LVar "a") (Const annz 99) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz))
                  (G.Escape annz 0)))) `G.sSeq`
             G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Escape annz 0)))

    evalProgItSuccess (101,[[]])
      [] (G.Func annz "(+)" (TypeF (TypeN [Type1 ["Int"], Type1 ["Int"]]) (Type1 ["Int"])) (G.Var annz "a" (Type1 ["Int"])
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Inp annz "A" (G.Trap annz (G.Par annz
                  (G.Var annz "b" (Type1 ["Int"]) (G.Write annz (LVar "b") (Const annz 99) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz))
                  (G.Escape annz 0)) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "(+)" (Tuple annz [(Read annz "a"),(Const annz 100)])) `G.sSeq`
            G.Escape annz 0))))

    evalProgItFail ["`loop` never iterates"]
      [] (G.Seq annz (G.Trap annz (G.Loop annz (G.Par annz
                 (G.Inp annz "A" (G.Var annz "x" (Type1 ["Int"]) (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz)))
                 (G.Escape annz 0)))) (G.Escape annz 0))

    evalProgItSuccess (1,[[]])
      [] (G.Seq annz (G.Trap annz (G.Par annz
                 (G.Inp annz "A" (G.Var annz "x" (Type1 ["Int"]) (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.AwaitInp annz "A" `G.sSeq` G.Halt annz)))
                 (G.Escape annz 0))) (G.Escape annz 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write annz (LVar "_ret") (Const annz 1)) `G.sSeq`
      (G.Evt annz "a"
        (G.Trap annz
        (G.Par annz
          ((G.AwaitEvt annz "a") `G.sSeq` (G.Write annz (LVar "_ret") (Const annz 5)) `G.sSeq` (G.Escape annz 0))
          ((G.EmitEvt annz "a") `G.sSeq` G.Halt annz)))) `G.sSeq`
      (G.Escape annz 0))

    evalProgItSuccess (5,[[]]) [] (
      (G.Write annz (LVar "_ret") (Const annz 1)) `G.sSeq`
      (G.Evt annz "a"
        (G.Trap annz (G.Par annz
          ((G.AwaitEvt annz "a") `G.sSeq` (G.Write annz (LVar "_ret") (Const annz 5)) `G.sSeq` (G.Escape annz 0))
          (G.Seq annz (G.Trap annz (G.Par annz (G.Fin annz (G.EmitEvt annz "a")) (G.Escape annz 0))) (G.Escape annz 0)))
      )) `G.sSeq` (G.Escape annz 0))

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
      (G.Var annz "x" (Type1 ["Int"]) (
        (G.Write annz (LVar "x") (Const annz 10)) `G.sSeq`
        (G.Trap annz (G.Par annz
          (G.Var annz "y" (Type1 ["Int"]) (G.Halt annz))
          (G.Seq annz (G.Write annz (LVar "x") (Const annz 99)) (G.Escape annz 0))
        )) `G.sSeq`
        (G.Write annz (LVar "_ret") (Read annz "x")) `G.sSeq`
        (G.Escape annz 0)
      )))

    it "input A ; event e ; pause " $
        compile_run
            (G.Seq annz (G.Seq annz
                (G.Var annz "x" (Type1 ["Int"])
                  (G.Seq annz
                    (G.Write annz (LVar "x") (Const annz 1))
                    (G.Evt annz "e"
                      (G.Trap annz (G.Par annz
                        (G.Inp annz "A" (G.Seq annz (G.AwaitInp annz "A") (G.Seq annz (G.Write annz (LVar "x") (Const annz 0)) (G.Seq annz (G.EmitEvt annz "e") (G.Halt annz)))))
                        (G.Seq annz (G.Pause annz "x" (G.Trap annz (G.Par annz (G.Seq annz (G.AwaitEvt annz "e") (G.Escape annz 0)) ((G.EmitEvt annz "e") `G.sSeq` (G.Halt annz))))) (G.Escape annz 0)))))))
                (G.Write annz (LVar "_ret") (Const annz 99))) (G.Escape annz 0))
            ["A"]
        `shouldBe` Right (99,[[],[]])

    -- multiple inputs

    it "await A ; escape 1" $
        compile_run
            (G.Inp annz "A" (G.AwaitInp annz "A" `G.sSeq` G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` (G.Escape annz 0)))
            ["A"]
        `shouldBe` Right (1,[[],[]])

    evalProgItFail ["program didn't terminate"]
      [] (G.Inp annz "A" (G.AwaitInp annz "A" `G.sSeq` G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.Escape annz 0))

    evalProgItFail ["program didn't terminate"]
      ["B"] (G.Inp annz "A" (G.AwaitInp annz "A" `G.sSeq` G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.Escape annz 0))

    evalProgItFail ["pending inputs"]
      ["A","A"] (G.Inp annz "A" (G.AwaitInp annz "A" `G.sSeq` G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.Escape annz 0))

    evalProgItSuccess (1,[[],[],[]])
      ["A","B"] (G.Inp annz "A" (G.Inp annz "B" (G.AwaitInp annz "A" `G.sSeq` G.AwaitInp annz "B" `G.sSeq` G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.Escape annz 0)))

    evalProgItSuccess (1,[[]]) [] (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq` G.Escape annz 0)

    -- multiple outputs

    describe "out:" $ do
        it "out O; emit O" $
            compile_run (G.Out annz "O" Type0 (G.Seq annz (G.EmitExt annz "O" (Unit annz)) (G.Seq annz (G.Write annz (LVar "_ret") (Const annz 1)) (G.Escape annz 0))))
                []
            `shouldBe` Right (1,[[("O",Nothing)]])

        it "I-F-O" $
            compile_run (G.Out annz "O" Type0 (G.Inp annz "I" (G.Inp annz "F" (G.Seq annz (G.Seq annz (G.Write annz (LVar "_ret") (Const annz 1)) (G.Trap annz (G.Par annz (G.Seq annz (G.AwaitInp annz "F") (G.Escape annz 0)) (G.Every annz "I" (G.EmitExt annz "O" (Unit annz)))))) (G.Escape annz 0)))))
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
