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

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

  describe "Env/Envs" $ do

      it "pass: 1st write" $
        envWrite [("x",Nothing)] "x" (Const annz 0) `shouldBe` [("x",Just (Const annz 0))]

      it "pass: 2nd write" $
        envWrite [("x",Just (Const annz 99))] "x" (Const annz 0) `shouldBe` [("x",Just (Const annz 0))]

      it "pass: write in middle" $
        envWrite [("a",Nothing),("x",Just (Const annz 99)),("b",Nothing)] "x" (Const annz 0) `shouldBe` [("a",Nothing),("x",Just (Const annz 0)),("b",Nothing)]

      it "pass: write in last" $
        envWrite [("a",Nothing),("b",Nothing),("x",Just (Const annz 99))] "x" (Const annz 0) `shouldBe` [("a",Nothing),("b",Nothing),("x",Just (Const annz 0))]

  describe "envRead vars id" $ do
      it "pass: read in simple env" $
        envRead [("x",Just (Const annz 0))] "x" `shouldBe` (Const annz 0)

      it "pass: read in complex env" $
        let vars = [("y",Just (Const annz 0)),("x",Just (Const annz 1)),("z",Just (Const annz 0))] in
          envRead vars "x" `shouldBe` (Const annz 1)

  describe "envEval vars exp" $ do
      it "pass: vars == [] && exp == (Const _)" $
        envEval [] (Const annz 0) `shouldBe` (Const annz 0)

      it "pass: eval in simple env" $
        let vars = [("x",Just (Const annz 1)),("y",Just (Const annz 2))] in
          envEval vars (Call annz "+" (Tuple annz [(Call annz "-" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
          `shouldBe` (Const annz (-4))

      it "pass: eval in complex env" $
        let vars = [("y",Just (Const annz 2)),("x",Just (Const annz 1)),("y",Just (Const annz 99)),("x",Just (Const annz 99))] in
          envEval vars (Call annz "+" (Tuple annz [(Call annz "-" (Tuple annz [(Read annz "x"),(Const annz 3)])),(Call annz "negate" (Read annz "y"))]))
          `shouldBe` (Const annz (-4))

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (Write "x" (Const annz 1)), [])
        `shouldBe` (Var ("x",(Just (Const annz 1))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Const annz 1))) (Write "x" (Const annz 2)), [])
        `shouldBe` (Var ("x",(Just (Const annz 2))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Write "x" (Const annz 1))), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Write "x" (Const annz 1)), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("x",(Just (Const annz 1)))
          (Var ("y",Nothing)
            (Write "y" (Call annz "+" (Tuple annz [(Read annz "x"),(Const annz 2)])))), []))
        `shouldBe` (Var ("x",(Just (Const annz 1))) (Var ("y",(Just (Const annz 3))) Nop), [])

      it "[x=1,y=?] y=x+2" $
        step
        (Var ("x",(Just (Const annz 1)))
        (Var ("y",Nothing)
          (Write "y" (Call annz "+" (Tuple annz [(Read annz "x"),(Const annz 2)])))), [])
        `shouldBe`
        (Var ("x",(Just (Const annz 1)))
        (Var ("y",(Just (Const annz 3))) Nop), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("x",(Just (Const annz 0)))
          (Write "x" (Call annz "negate" (Call annz "+" (Tuple annz [(Const annz 5),(Const annz 1)])))), [])
        `shouldBe`
        (Var ("x",(Just (Const annz (-6)))) Nop, [])

  describe "seq" $ do
      it "nop" $
        step (Seq Nop Nop, [])
        `shouldBe` (Nop, [])
      it "adv" $
        step (Seq (Seq Nop Nop) Nop, [])
        `shouldBe` (Seq Nop Nop, [])

  describe "if" $ do
      it "x == 0" $
        step (If (Read annz "x") Nop Nop, [("x",Just (Const annz 0))])
        `shouldBe` (Nop, [("x",Just (Const annz 0))])
      it "x /= 0" $
        step (If (Read annz "x") Nop Nop, [("x",Just (Const annz 1))])
        `shouldBe` (Nop, [("x",Just (Const annz 1))])

  describe "loop" $ do
      it "nop" $
        step (Loop' Nop Nop, [])
        `shouldBe` (Loop' Nop Nop, [])
{-
  describe "(Loop' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        step (Loop' (Escape 0) Nop, [])
        `shouldBe` (Escape 0, [])

      it "pass: lvl > 0" $
        step (Loop' (Escape 0) (Seq (EmitEvt "z") Nop), [])
        `shouldBe` ((Escape 0), [])
-}
      it "adv" $
        step (Loop' (Seq Nop Nop) Nop, [])
        `shouldBe` (Loop' Nop Nop, [])

  --------------------------------------------------------------------------
  describe "go" $ do

    evalProgItSuccess (Const annz 11)
      (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Ret   annz (Call annz "+" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (Const annz 11)
      (G.Func annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int")) (G.Var annz "a" (Type1 "Int")
           (G.Write annz (LVar "a") (Const annz 1) `G.sSeq`
            G.Var annz "b" (Type1 "Int") (G.Write annz (LVar "b") (Const annz 99)) `G.sSeq`
            G.Ret annz (Call annz "+" (Tuple annz [(Read annz "a"),(Const annz 10)])) `G.sSeq`
            G.Nop annz)))

    evalProgItSuccess (Const annz 1)
      (G.Ret annz (Const annz 1) `G.sSeq`
          G.Var annz "_" (Type1 "Int") (G.Ret annz (Const annz 2)) `G.sSeq`
          G.Nop annz)

{-
    describe "typesystem:" $ do

        it "id(1)" $
            go
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
            go
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
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (G.prelude annz p) `shouldBe` res))
