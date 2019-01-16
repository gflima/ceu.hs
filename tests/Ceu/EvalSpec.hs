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
        let vars = [("negate__(Int -> Int)",Nothing), ("+__((Int,Int) -> Int)",Nothing), ("-__((Int,Int) -> Int)",Nothing),
                    ("x",Just (Number 1)),("y",Just (Number 2))] in
          envEval vars (Call (Read "+__((Int,Int) -> Int)") (Tuple [(Call (Read "-__((Int,Int) -> Int)") (Tuple [(Read "x"),(Number 3)])),(Call (Read "negate__(Int -> Int)") (Read "y"))]))
          `shouldBe` (Number (-4))

      it "pass: eval in complex env" $
        let vars = [("negate__(Int -> Int)",Nothing), ("+__((Int,Int) -> Int)",Nothing), ("-__((Int,Int) -> Int)",Nothing),
                    ("y",Just (Number 2)),("x",Just (Number 1)),
                    ("y",Just (Number 99)),("x",Just (Number 99))] in
          envEval vars (Call (Read "+__((Int,Int) -> Int)") (Tuple [(Call (Read "-__((Int,Int) -> Int)") (Tuple [(Read "x"),(Number 3)])),(Call (Read "negate__(Int -> Int)") (Read "y"))]))
          `shouldBe` (Number (-4))

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (Write (LVar "x") (Number 1)), [])
        `shouldBe` (Var ("x",(Just (Number 1))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Number 1))) (Write (LVar "x") (Number 2)), [])
        `shouldBe` (Var ("x",(Just (Number 2))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Write (LVar "x") (Number 1))), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Write (LVar "x") (Number 1)), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("+__((Int,Int) -> Int)",Nothing)
          (Var ("x",(Just (Number 1)))
          (Var ("y",Nothing)
          (Write (LVar "y") (Call (Read "+__((Int,Int) -> Int)") (Tuple [(Read "x"),(Number 2)])))))), [])
        `shouldBe` (Var ("+__((Int,Int) -> Int)",Nothing) (Var ("x",(Just (Number 1))) (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (Var ("+__((Int,Int) -> Int)",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",Nothing)
          (Write (LVar "y") (Call (Read "+__((Int,Int) -> Int)") (Tuple [(Read "x"),(Number 2)]))))), [])
        `shouldBe`
        (Var ("+__((Int,Int) -> Int)",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("negate__(Int -> Int)",Nothing)
        (Var ("+__((Int,Int) -> Int)",Nothing)
        (Var ("x",(Just (Number 0)))
          (Write (LVar "x") (Call (Read "negate__(Int -> Int)") (Call (Read "+__((Int,Int) -> Int)") (Tuple [(Number 5),(Number 1)])))))), [])
        `shouldBe`
        (Var ("negate__(Int -> Int)",Nothing)
        (Var ("+__((Int,Int) -> Int)",Nothing)
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

  describe "func" $ do
    it "ret f()" $
      steps (
        (Var ("f", Just $ Func (Ret (Number 1)))
        (Ret (Call (Read "f") Unit)))
        , [])
      `shouldBe` (Number 1)

    it "ret f(1)" $
      steps (
        (Var ("+__((Int,Int) -> Int)", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+__((Int,Int) -> Int)") (Tuple [Read "_arg",Number 1]))))
        (Ret (Call (Read "f") (Number 2)))))
        , [])
      `shouldBe` (Number 3)

    it "ret f(1,2)" $
      steps (
        (Var ("+__((Int,Int) -> Int)", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+__((Int,Int) -> Int)") (Read "_arg"))))
        (Ret (Call (Read "f") (Tuple [Number 1,Number 2])))))
        , [])
      `shouldBe` (Number 3)

  --------------------------------------------------------------------------
  describe "go" $ do

    describe "write" $ do

      it "(a,b) <- (1,2)" $
        go
          (B.Data annz "Int" [] [] False
          (B.Var annz "a" TypeT
          (B.Var annz "b" TypeT
          (B.Seq annz
          (B.Write annz (LTuple [LVar "a",LVar "b"]) (B.Tuple annz [B.Number annz 1,B.Number annz 2]))
          (B.Ret annz (B.Read annz "b"))))))
          `shouldBe` (Number 2)

    describe "func" $ do

      it "Int ; f1 ; return f1 1" $
        go
          (B.Data annz "Int" [] [] False
          (B.Var annz "f1" (TypeF Type0 (Type1 "Int"))
          (B.Seq annz
          (B.Write annz
            (LVar "f1")
            (B.Func annz (TypeF Type0 (Type1 "Int"))
              (B.Ret annz (B.Number annz 1))))
          (B.Ret annz (B.Call annz (B.Read annz "f1") (B.Unit annz))))))
        `shouldBe` (Number 1)

      it "(f,g) <- (+,c) ; return f(g 1, g 2)" $
        go
          (B.Data annz "Int" [] [] False
          (B.Var annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
          (B.Var annz "c" (TypeF (Type1 "Int") (Type1 "Int"))
          (B.Seq annz
          (B.Write annz
            (LVar "c")
            (B.Func annz (TypeF (Type1 "Int") (Type1 "Int"))
              (B.Ret annz (B.Arg annz))))
          (B.Var annz "f" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
          (B.Var annz "g" (TypeF (Type1 "Int") (Type1 "Int"))
          (B.Seq annz
          (B.Write annz (LTuple [LVar "f",LVar "g"]) (B.Tuple annz [B.Read annz "+",B.Read annz "c"]))
          (B.Ret annz
            (B.Call annz
              (B.Read annz "f")
              (B.Tuple annz [
                B.Call annz (B.Read annz "c") (B.Number annz 1),
                B.Call annz (B.Read annz "c") (B.Number annz 2)]))))))))))
          `shouldBe` (Number 3)

    describe "class" $ do

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f2 1" $
        go
          (B.Data annz "Int" [] [] False
          (B.Var annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
          (B.Data annz "Bool" [] [] False
          (B.Class annz "X" ["a"]
            (B.Var annz "f2" (TypeF (TypeV "a") (Type1 "Int")) (B.Nop annz))
          (B.Inst annz "X" [Type1 "Bool"]
            (B.Var annz "f2" (TypeF (Type1 "Bool") (Type1 "Int"))
            (B.Seq annz
            (B.Write annz
              (LVar "f2")
              (B.Func annz (TypeF (Type1 "Bool") (Type1 "Int"))
                (B.Ret annz (B.Number annz 0))))
            (B.Nop annz)))
          (B.Inst annz "X" [Type1 "Int"]
            (B.Var annz "f2" (TypeF (Type1 "Int") (Type1 "Int"))
            (B.Seq annz
            (B.Write annz
              (LVar "f2")
              (B.Func annz (TypeF (Type1 "Int") (Type1 "Int"))
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "+")
                    (B.Tuple annz [B.Arg annz, B.Number annz 1])))))
            (B.Nop annz)))
          (B.Var annz "ret" (Type1 "Int")
          (B.Seq annz
          (B.Write annz (LVar "ret")
            (B.Call annz (B.Read annz "f2") (B.Number annz 1)))
          (B.Ret annz (B.Read annz "ret"))))))))))
        `shouldBe` (Number 2)

      it "Int ; X a ; inst X Int ; return f3 1" $
        go
          (B.Data annz "Int" [] [] False
          (B.Class annz "X" ["a"]
            (B.Var annz "f3" (TypeF (TypeV "a") (Type1 "Int")) (B.Nop annz))
          (B.Inst annz "X" [Type1 "Int"]
            (B.Var annz "f3" (TypeF (Type1 "Int") (Type1 "Int"))
            (B.Seq annz
            (B.Write annz
              (LVar "f3")
              (B.Func annz (TypeF (Type1 "Int") (Type1 "Int"))
                (B.Ret annz (B.Number annz 1))))
            (B.Nop annz)))
          (B.Ret annz (B.Call annz (B.Read annz "f3") (B.Number annz 1))))))
        `shouldBe` (Number 1)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f4 1" $
        go
          (B.Data annz "Int" [] [] False
          (B.Var annz "+" (TypeF (TypeN [Type1 "Int", Type1 "Int"]) (Type1 "Int"))
          (B.Data annz "Bool" [] [] False
          (B.Class annz "X" ["a"]
            (B.Var annz "f4" (TypeF (TypeV "a") (Type1 "Int")) (B.Nop annz))
          (B.Inst annz "X" [Type1 "Bool"]
            (B.Var annz "f4" (TypeF (Type1 "Bool") (Type1 "Int"))
            (B.Seq annz
            (B.Write annz
              (LVar "f4")
              (B.Func annz (TypeF (Type1 "Bool") (Type1 "Int"))
                (B.Ret annz (B.Number annz 0))))
            (B.Nop annz)))
          (B.Inst annz "X" [Type1 "Int"]
            (B.Var annz "f4" (TypeF (Type1 "Int") (Type1 "Int"))
            (B.Seq annz
            (B.Write annz
              (LVar "f4")
              (B.Func annz (TypeF (Type1 "Int") (Type1 "Int"))
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "+")
                    (B.Tuple annz [B.Arg annz, B.Number annz 1])))))
              (B.Nop annz)))
          (B.Ret annz (B.Call annz (B.Read annz "f4") (B.Number annz 1)))))))))
        `shouldBe` (Number 2)

    describe "misc" $ do

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

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
