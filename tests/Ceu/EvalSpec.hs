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
  rnf (Const _ _)   = ()
  rnf (Read  _ _)   = ()
  rnf (Unit  _)     = ()
  rnf (Tuple _ _)   = ()
  rnf (Call  _ _ _) = ()

instance NFData Stmt where
  rnf (Write _ expr) = rnf expr
  rnf (If expr p q)  = rnf expr `deepseq` rnf p `deepseq` rnf q
  rnf (Seq p q)      = rnf p `deepseq` rnf q
  rnf (Nop)          = ()
  rnf (Var _ p)      = rnf p
  rnf (Loop' p q)    = rnf p

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
          varsEval vars (Call annz "+" (Tuple annz [(Call annz "-" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
          `shouldBe` (-4)

      it "pass: eval in complex env" $
        let vars = [("y",Just 2),("x",Just 1),("y",Just 99),("x",Just 99)] in
          varsEval vars (Call annz "+" (Tuple annz [(Call annz "-" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
          `shouldBe` (-4)

  --------------------------------------------------------------------------
  describe "step" $ do

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
            (Write "y" (Call annz "+" (Tuple annz [(Read annz "x"),(Const annz 2)])))), 0, [], [], []))
        `shouldBe` (Var ("x",(Just 1)) (Var ("y",(Just 3)) Nop),0,[],[], [])

      it "pass: [x=1,y=?] y=x+2" $
        step
        (Var ("x",(Just 1))
        (Var ("y",Nothing)
          (Write "y" (Call annz "+" (Tuple annz [(Read annz "x"),(Const annz 2)])))), 0, [], [], [])
        `shouldBe`
        (Var ("x",(Just 1))
        (Var ("y",(Just 3)) Nop), 0, [], [], [])

      it "pass: [x=?] x=-(5+1)" $
        step
        (Var ("x",(Just 0))
          (Write "x" (Call annz "negate" (Call annz "+" (Tuple annz [(Const annz 5),(Const annz 1)])))), 0, [], [], [])
        `shouldBe`
        (Var ("x",(Just (-6))) Nop, 0, [], [], [])

  -- seq-nop --
  describe "(Seq Nop q)" $ do
      it "pass: lvl == 0" $
        step (Seq Nop Nop, 0, [], [], [])
        `shouldBe` (Nop, 0, [], [], [])

  -- seq-adv --
  describe "(Seq p q)" $ do
      it "pass: lvl == 0" $
        step (Seq (Seq Nop Nop) Nop, 0, [], [], [])
        `shouldBe` (Seq Nop Nop, 0, [], [], [])

  -- if-true/false --
  describe "(If exp p q)" $ do
      it "fail: undeclared variable" $
        forceEval (step (If (Read annz "x") Nop Nop, 0, [], [], []))
        `shouldThrow` errorCall "varsRead: undeclared variable: x"

      it "pass: x == 0" $
        step (If (Read annz "x") Nop Nop, 0, [("x",Just 0)], [], [])
        `shouldBe` (Nop, 0, [("x",Just 0)], [], [])

      it "pass: x /= 0" $
        step (If (Read annz "x") Nop Nop, 0, [("x",Just 1)], [], [])
        `shouldBe` (Nop, 0, [("x",Just 1)], [], [])

  -- loop-nop --
  describe "(Loop' Nop q)" $ do
      it "pass: lvl == 0" $
        step (Loop' Nop Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

{-
  -- loop-brk --
  describe "(Loop' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Escape 0) Nop, 0, [], [], [])
        `shouldBe` (Escape 0, 0, [], [], [])

      it "pass: lvl > 0" $
        step (Loop' (Escape 0) (Seq (EmitEvt "z") Nop), 3, [], [], [])
        `shouldBe` ((Escape 0), 3, [], [], [])
-}

  -- loop-adv --
  describe "(Loop' p q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Seq Nop Nop) Nop, 0, [], [], [])
        `shouldBe` (Loop' Nop Nop, 0, [], [], [])

  --------------------------------------------------------------------------
  describe "steps" $ do
    describe "zero steps (no step-rule applies)" $ do

      stepsItPass
        (Nop, 0, [], [], [])
        (Nop, 0, [], [], [])

    describe "one+ steps" $ do

      stepsItPass
        (Var ("x",Nothing) (Write "x" (Const annz 0)), 3, [], [], [])
        (Nop, 0, [], [], [])

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
      it "pass: lvl>0, but `Nop`" $
        let d = (Nop, 13, [], [], []) in
          (steps d `shouldBe` (Nop, 0, [], [], []))
          >> (isReducible d `shouldBe` True)

  --------------------------------------------------------------------------
  describe "compile_run" $ do

    evalProgItSuccess (11,[[]])
      [] (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "+" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (11,[[]])
      [] (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Var annz "b" (Type1 "Int") (G.Write annz (LVar "b") (Const annz 99)) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "+" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItFail ["variable 'a' is already declared"]
      [] (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Var annz "a" (Type1 "Int") (G.Write annz (LVar "a") (Const annz 99)) `G.sSeq`
            G.Write annz (LVar "_ret") (Call annz "+" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (2,[[]])
      [] (G.Write annz (LVar "_ret") (Const annz 1) `G.sSeq`
          G.Var annz "_" (Type1 "Int") (G.Write annz (LVar "_ret") (Const annz 2)) `G.sSeq`
          G.Nop annz)

{-
    describe "typesystem:" $ do

        it "id(1)" $
            compile_run
                (G.FuncI annz "id"
                    (TypeF (Type1 "Int") (Type1 "Int"))
                    (G.Var annz "_fret" (Type1 "Int")
                        (G.Write annz (LVar "_ret") (Read annz "_arg_0")))
                (G.Seq annz
                    (G.Write annz (LVar "_ret") (Call annz "id" (Const annz 1)))
                    (G.Escape annz 0)))
                []
            `shouldBe` Right (1,[[]])

        it "Int ; Bool ; Equalable a ; inst Equalable Bool/Int ; fff 1" $
            compile_run
                (G.Data annz "Bool" [] [] False
                (G.Class annz "Equalable" ["a"]
                    (G.Func annz "fff" (TypeF (TypeV "a") (Type1 "Int")) (G.Nop annz))
                (G.Inst annz "Equalable" ["Bool"]
                    (G.Func annz "fff" (TypeF (Type1 "Bool") (Type1 "Int")) (G.Nop annz))
                (G.Inst annz "Equalable" ["Int"]
                    (G.Func annz "fff" (TypeF (Type1 "Int") (Type1 "Int")) (G.Nop annz))
                (G.Seq annz
                    (G.Write annz (LVar "_ret") (Call annz "fff" (Const annz 1)))
                    (G.Escape annz 0))))))
                []
            `shouldBe` Right (1,[[]])
-}

      where
        stepsItPass (p,n,e,vars,outs) (p',n',e',vars',outs') =
          (it (printf "pass: %s -> %s#" "todo" "todo")
           ((steps (p,n,e,vars,outs) `shouldBe` (p',n',e',vars',outs'))
             >> ((isReducible (p',n',e',vars',outs')) `shouldBe` False)))

        stepsItFail err (p,n,e,vars,outs) =
          (it (printf "fail: %s ***%s" "todo" err)
           (forceEval (steps (p,n,e,vars,outs)) `shouldThrow` errorCall err))

        reactionItPass (p,e,vars) (p',vars',outs') =
          (it (printf "pass: %s | %s -> %s" e "todo" "todo")
            (reaction p e `shouldBe` (p',outs')))

        evalProgItSuccess (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) "todo" res (show outss)) $
            (compile_run prog hist `shouldBe` Right (res,outss)))

        evalProgItFail err hist prog =
          (it (printf "pass: %s | %s ***%s" (show hist) "todo" (show err)) $
            (compile_run prog hist `shouldBe` Left err))
