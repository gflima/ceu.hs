module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Ann      (annz)
import qualified Ceu.Grammar.Basic as B
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf
import Debug.Trace

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

  describe "Env/Envs" $ do

      it "pass: 1st write" $
        envWrite [("x",Nothing)] "x" (Number 0) `shouldBe` [("x",Just (Number 0))]

      it "pass: 2nd write" $
        envWrite [("x",Just (Number 99))] "x" (Number 0) `shouldBe` [("x",Just (Number 0))]

      it "pass: write in middle" $
        envWrite [("a",Nothing),("x",Just (Number 99)),("b",Nothing)] "x" (Number 0) `shouldBe` [("a",Nothing),("x",Just (Number 0)),("b",Nothing)]

      it "pass: write in last" $
        envWrite [("a",Nothing),("b",Nothing),("x",Just (Number 99))] "x" (Number 0) `shouldBe` [("a",Nothing),("b",Nothing),("x",Just (Number 0))]

  describe "envRead vars id" $ do
      it "pass: read in simple env" $
        envRead [("x",Just (Number 0))] "x" `shouldBe` (Number 0)

      it "pass: read in complex env" $
        let vars = [("y",Just (Number 0)),("x",Just (Number 1)),("z",Just (Number 0))] in
          envRead vars "x" `shouldBe` (Number 1)

  describe "envEval vars exp" $ do
      it "pass: vars == [] && exp == (Number _)" $
        envEval [] (Number 0) `shouldBe` (Number 0)

      it "pass: eval in simple env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("x",Just (Number 1)),("y",Just (Number 2))] in
          envEval vars (Call (Read "+") (Tuple [(Call (Read "-") (Tuple [(Read "x"),(Number 3)])),(Call (Read "negate") (Read "y"))]))
          `shouldBe` (Number (-4))

      it "pass: eval in complex env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("y",Just (Number 2)),("x",Just (Number 1)),
                    ("y",Just (Number 99)),("x",Just (Number 99))] in
          envEval vars (Call (Read "+") (Tuple [(Call (Read "-") (Tuple [(Read "x"),(Number 3)])),(Call (Read "negate") (Read "y"))]))
          `shouldBe` (Number (-4))

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (Write "x" (Number 1)), [])
        `shouldBe` (Var ("x",(Just (Number 1))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Number 1))) (Write "x" (Number 2)), [])
        `shouldBe` (Var ("x",(Just (Number 2))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Write "x" (Number 1))), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Write "x" (Number 1)), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("+",Nothing)
          (Var ("x",(Just (Number 1)))
          (Var ("y",Nothing)
          (Write "y" (Call (Read "+") (Tuple [(Read "x"),(Number 2)])))))), [])
        `shouldBe` (Var ("+",Nothing) (Var ("x",(Just (Number 1))) (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (Var ("+",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",Nothing)
          (Write "y" (Call (Read "+") (Tuple [(Read "x"),(Number 2)]))))), [])
        `shouldBe`
        (Var ("+",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (Number 0)))
          (Write "x" (Call (Read "negate") (Call (Read "+") (Tuple [(Number 5),(Number 1)])))))), [])
        `shouldBe`
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (Number (-6)))) Nop)), [])

  describe "seq" $ do
      it "nop" $
        step (Seq Nop Nop, [])
        `shouldBe` (Nop, [])
      it "adv" $
        step (Seq (Seq Nop Nop) Nop, [])
        `shouldBe` (Seq Nop Nop, [])

  describe "if" $ do
      it "x == 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 0))])
        `shouldBe` (Nop, [("x",Just (Number 0))])
      it "x /= 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 1))])
        `shouldBe` (Nop, [("x",Just (Number 1))])

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

    describe "func" $ do
      it "ret f()" $
        steps (
          (Var ("f", Just $ Func (Ret (Number 1)))
          (Ret (Call (Read "f") Unit)))
          , [])
        `shouldBe` (Number 1)

    evalProgItSuccess (Number 11)
      (B.Var annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
      (B.Var annz "a" (Type1 "Int")
      (B.Seq annz
      (B.Write annz (LVar "a") (B.Number annz 1))
      (B.Ret annz (B.Call annz (B.Read annz "+") (B.Tuple annz [(B.Read annz "a"),(B.Number annz 10)]))))))

    evalProgItSuccess (Number 11)
      (B.Var annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
      (B.Var annz "a" (Type1 "Int")
      (B.Seq annz
      (B.Write annz (LVar "a") (B.Number annz 1))
      (B.Var annz "b" (Type1 "Int")
      (B.Seq annz
      (B.Write annz (LVar "b") (B.Number annz 99))
      (B.Ret annz
        (B.Call annz (B.Read annz "+")
                     (B.Tuple annz [(B.Read annz "a"),(B.Number annz 10)]))))))))

    evalProgItSuccess (Number 1)
      (B.Ret annz (B.Number annz 1) `B.sSeq`
          B.Var annz "_" (Type1 "Int") (B.Ret annz (B.Number annz 2)) `B.sSeq`
          B.Nop annz)

{-
    describe "typesystem:" $ do

        it "id(1)" $
            go
                (B.FuncI annz "id"
                    (TypeF (Type1 "Int") (Type1 "Int"))
                    (B.Var annz "_fret" (Type1 "Int")
                        (B.Write annz (LVar "_ret") (Read annz "_arg_0")))
                (B.Seq annz
                    (B.Write annz (LVar "_ret") (SCall annz "id" (Number annz 1)))
                    (B.Escape annz 0)))
                []
            `shouldBe` Right (1,[[]])

        it "Int ; Bool ; Equalable a ; inst Equalable Bool/Int ; fff 1" $
            go
                (B.Data annz "Bool" [] [] False
                (B.Class annz "Equalable" ["a"]
                    (B.Func annz "fff" (TypeF (TypeV "a") (Type1 "Int")) (B.Nop annz))
                (B.Inst annz "Equalable" ["Bool"]
                    (B.Func annz "fff" (TypeF (Type1 "Bool") (Type1 "Int")) (B.Nop annz))
                (B.Inst annz "Equalable" ["Int"]
                    (B.Func annz "fff" (TypeF (Type1 "Int") (Type1 "Int")) (B.Nop annz))
                (B.Seq annz
                    (B.Write annz (LVar "_ret") (B.SCall annz "fff" (B.Number annz 1)))
                    (B.Escape annz 0))))))
                []
            `shouldBe` Right (1,[[]])
-}

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
