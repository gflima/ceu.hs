module Ceu.EvalSpec (main, spec) where

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..))
import Ceu.Grammar.Ann      (annz)
import qualified Ceu.Grammar.Basic as B
import Ceu.Eval
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf
import Debug.Trace

int  = TypeD ["Int"]  [] Type0
bool = TypeD ["Bool"] [] Type0

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
        step (Var ("x",Nothing) (Match (LVar "x") (Number 1) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (Number 1))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Number 1))) (Match (LVar "x") (Number 2) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (Number 2))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Match (LVar "x") (Number 1) Nop Nop)), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Match (LVar "x") (Number 1) Nop Nop), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("+",Nothing)
          (Var ("x",(Just (Number 1)))
          (Var ("y",Nothing)
          (Match (LVar "y") (Call (Read "+") (Tuple [(Read "x"),(Number 2)])) Nop Nop)))), [])
        `shouldBe` (Var ("+",Nothing) (Var ("x",(Just (Number 1))) (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (Var ("+",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",Nothing)
          (Match (LVar "y") (Call (Read "+") (Tuple [(Read "x"),(Number 2)])) Nop Nop))), [])
        `shouldBe`
        (Var ("+",Nothing)
        (Var ("x",(Just (Number 1)))
        (Var ("y",(Just (Number 3))) Nop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (Number 0)))
          (Match (LVar "x") (Call (Read "negate") (Call (Read "+") (Tuple [(Number 5),(Number 1)]))) Nop Nop))), [])
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

{-
  describe "if" $ do
      it "x == 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 0))])
        `shouldBe` (Nop, [("x",Just (Number 0))])
      it "x /= 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Number 1))])
        `shouldBe` (Nop, [("x",Just (Number 1))])
-}

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
        , [("_steps",Just $ Number 0)])
      `shouldBe` (Number 1)

    it "ret f(1)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+") (Tuple [Read "_arg",Number 1]))))
        (Ret (Call (Read "f") (Number 2)))))
        , [("_steps",Just $ Number 0)])
      `shouldBe` (Number 3)

    it "ret f(1,2)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+") (Read "_arg"))))
        (Ret (Call (Read "f") (Tuple [Number 1,Number 2])))))
        , [("_steps",Just $ Number 0)])
      `shouldBe` (Number 3)

  --------------------------------------------------------------------------
  describe "go" $ do

    describe "write" $ do

      it "(a,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TypeT,cz)
          (B.Var annz "b" (TypeT,cz)
          (B.Match annz False (B.LTuple [B.LVar "a",B.LVar "b"]) (B.Tuple annz [B.Number annz 1,B.Number annz 2])
            (B.Ret annz (B.Read annz "b"))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Number 2)

      it "(_,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TypeT,cz)
          (B.Var annz "b" (TypeT,cz)
          (B.Match annz False (B.LTuple [B.LAny,B.LVar "b"]) (B.Tuple annz [B.Number annz 1,B.Number annz 2])
            (B.Ret annz (B.Read annz "b"))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Number 2)

      it "1 <- 1" $
        go
          (B.Data annz (int,cz) False
          (B.Match annz False (B.LNumber 1) (B.Number annz 1)
            (B.Ret annz (B.Number annz 2))
            (B.Ret annz (B.Error annz 99))))
          `shouldBe` (Number 2)

      it "a <- 1 ; `a` <- 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Number annz 1)
            (B.Match annz True (B.LExp $ B.Read annz "a") (B.Number annz 1)
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 99)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Number 1)

      it "a <- 2 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Number annz 2)
            (B.Match annz True (B.LNumber 1) (B.Read annz "a")
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 10)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Error 10)

      it "a <- 1 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Number annz 1)
            (B.Match annz True (B.LNumber 1) (B.Read annz "a")
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 99)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Number 1)

      it "a <- 1 ; `a` <- 2" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Number annz 1)
            (B.Match annz True (B.LExp $ B.Read annz "a") (B.Number annz 2)
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 10)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Error 10)

    describe "func" $ do

      it "Int ; f1 ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TypeF Type0 (int),cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TypeF Type0 (int),cz)
                          (B.Ret annz (B.Number annz 1)))
            (B.Ret annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
            (B.Ret annz (B.Error annz 99)))))
        `shouldBe` (Number 1)

      it "Int ; f1 (err!) ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TypeF Type0 Type0,cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TypeF Type0 Type0,cz)
                          (B.Ret annz (B.Error annz 1)))
            (B.Ret annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
            (B.Ret annz (B.Error annz 99)))))
        `shouldBe` (Error 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TypeF Type0 Type0,cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TypeF Type0 Type0,cz)
                          (B.Ret annz (B.Error annz 1)))
            (B.Seq annz
              (B.CallS annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
              (B.Ret annz (B.Number annz 99)))
            (B.Ret annz (B.Error annz 99)))))
        `shouldBe` (Error 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.Seq annz
            (B.CallS annz (B.Call annz (B.Error annz 1) (B.Unit annz)))
            (B.Ret annz (B.Error annz 99)))
        `shouldBe` (Error 1)

      it "(f,g) <- (+,c) ; return f(g 1, g 2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
          (B.Var annz "c" (TypeF (int) (int),cz)
          (B.Match annz False (B.LVar "c")
                        (B.Func annz (TypeF (int) (int),cz)
                          (B.Ret annz (B.Arg annz)))
            (B.Var annz "f" (TypeF (TypeN [int, int]) (int),cz)
              (B.Var annz "g" (TypeF (int) (int),cz)
              (B.Match annz False (B.LTuple [B.LVar "f",B.LVar "g"]) (B.Tuple annz [B.Read annz "+",B.Read annz "c"])
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "f")
                    (B.Tuple annz [
                      B.Call annz (B.Read annz "c") (B.Number annz 1),
                      B.Call annz (B.Read annz "c") (B.Number annz 2)])))
                (B.Ret annz (B.Error annz 99)))))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Number 3)

      it "glb <- 1 ; f () -> glb ; ret glb" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (B.Match annz False (B.LVar "glb") (B.Number annz 1)
            (B.Var   annz "f" (TypeF Type0 (int),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TypeF Type0 (int),cz)
                              (B.Ret annz (B.Read annz "glb")))
                (B.Ret annz
                  (B.Call annz (B.Read annz "f") (B.Unit annz)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99)))))
          `shouldBe` (Number 1)

      it "glb <- 1 ; f() -> g() -> glb ; ret f()()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (B.Match annz False (B.LVar "glb") (B.Number annz 1)
            (B.Var   annz "f" (TypeF Type0 (TypeF Type0 (int)),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TypeF Type0 (TypeF Type0 (int)),cz)
                              (B.Ret annz
                                (B.Func annz (TypeF Type0 (int),cz)
                                  (B.Ret annz (B.Read annz "glb")))))
                (B.Ret annz
                  (B.Call annz
                    (B.Call annz (B.Read annz "f") (B.Unit annz))
                    (B.Unit annz)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99)))))
          `shouldBe` (Number 1)

      it "(TODO: loc lifetime) g' <- nil ; { loc <- 1 ; f() -> g() -> glb ; g' <- f() } ; ret g'()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "g'" (TypeF Type0 (int),cz)
          (B.Var   annz "loc" (int,cz)
          (B.Match annz False (B.LVar "loc") (B.Number annz 1)
            (B.Var   annz "f" (TypeF Type0 (TypeF Type0 (int)),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TypeF Type0 (TypeF Type0 (int)),cz)
                              (B.Ret annz
                                (B.Func annz (TypeF Type0 (int),cz)
                                  (B.Ret annz (B.Read annz "loc")))))
                (B.Match annz False (B.LVar "g'")
                              (B.Call annz (B.Read annz "f") (B.Unit annz))
                  (B.Ret annz
                    (B.Call annz (B.Read annz "g'") (B.Unit annz)))
                  (B.Ret annz (B.Error annz 99)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Number 1)

    describe "data" $ do

      it "data X with Int ; x <- X 1 ; return x" $
        go
          (B.Data annz (int,cz) False
          (B.Data annz (TypeD ["X"] [] int,cz) False
          (B.Var annz "x" (TypeD ["X"] [] (int),cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Number annz 1))
            (B.Ret annz (B.Read annz "x"))
            (B.Ret annz (B.Error annz 99))))))
        `shouldBe` (Cons' ["X"] (Number 1))

      it "data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
          (B.Data annz (TypeD ["X"] [] (TypeN [int, int]),cz) False
          (B.Var annz "x" (TypeD ["X"] [] (TypeN [int, int]),cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Tuple annz [B.Call annz (B.Read annz "+") (B.Tuple annz [B.Number annz 1,B.Number annz 2]), B.Number annz 3]))
            (B.Ret annz (B.Read annz "x"))
            (B.Ret annz (B.Error annz 99)))))))
        `shouldBe` (Cons' ["X"] (Tuple [Number 3,Number 3]))

      it "TODO (coerse): data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
          (B.Data annz (TypeD ["X"] [] (TypeN [int, int]),cz) False
          (B.Var annz "x" (TypeD ["X"] [] Type0,cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Tuple annz [B.Number annz 1,B.Number annz 2]))
            (B.Ret annz (B.Call annz (B.Read annz "+") (B.Read annz "x")))
            (B.Ret annz (B.Error annz 99)))))))
        `shouldBe` (Cons' ["X"] (Number 1))

      it "data X with Int ; x:Int ; X x <- X 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Data  annz (TypeD ["X"] [] int,cz) False
          (B.Var   annz "x" (int,cz)
          (B.Match annz False (B.LCons ["X"] (B.LVar "x")) (B.Call annz (B.Cons annz ["X"]) (B.Number annz 1))
            (B.Ret   annz (B.Read annz "x"))
            (B.Ret   annz (B.Error annz 99))))))
        `shouldBe` (Number 1)

    describe "class" $ do

      it "Int ; X a ; inst X Int ; return f3 1" $
        go
          (B.Data annz (int,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f3",(TypeF (TypeV "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f3" (TypeF (TypeV "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (int,cz)
            [(annz,"f3",(TypeF (int) (int),cz),True)]
            (B.Var annz "$f3$(Int -> Int)$" (TypeF (int) (int),cz)
            (B.Match annz False
              (B.LVar "$f3$(Int -> Int)$")
              (B.Func annz (TypeF (int) (int),cz)
                (B.Ret annz (B.Number annz 1)))
              (B.Seq annz
                (B.Nop annz)
                (B.Ret annz (B.Call annz (B.Read annz "f3") (B.Number annz 1))))
              (B.Nop annz)))))))
        `shouldBe` (Number 1)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f2 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
          (B.Data annz (bool,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f2",(TypeF (TypeV "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f2" (TypeF (TypeV "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (bool,cz)
            [(annz,"f2",(TypeF (bool) (int),cz),True)]
            (B.Var annz "$f2$(Bool -> Int)$" (TypeF (bool) (int),cz)
            (B.Match annz False
              (B.LVar "$f2$(Bool -> Int)$")
              (B.Func annz (TypeF (bool) (int),cz)
                (B.Ret annz (B.Number annz 0)))
              (B.Seq annz
                (B.Nop annz)
                (B.Inst annz "X" (int,cz)
                  [(annz,"f2",(TypeF (int) (int),cz),True)]
                  (B.Var annz "$f2$(Int -> Int)$" (TypeF (int) (int),cz)
                  (B.Match annz False
                    (B.LVar "$f2$(Int -> Int)$")
                    (B.Func annz (TypeF (int) (int),cz)
                      (B.Ret annz
                        (B.Call annz
                          (B.Read annz "+")
                          (B.Tuple annz [B.Arg annz, B.Number annz 1]))))
                    (B.Seq annz
                      (B.Nop annz)
                      (B.Var annz "ret" (int,cz)
                      (B.Match annz False (B.LVar "ret")
                        (B.Call annz (B.Read annz "f2") (B.Number annz 1))
                        (B.Ret annz (B.Read annz "ret"))
                        (B.Ret annz (B.Error annz 99))))
                    )
                    (B.Nop annz))))
                    )
                    (B.Nop annz)))))))))
        `shouldBe` (Number 2)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f4 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
          (B.Data annz (bool,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f4",(TypeF (TypeV "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f4" (TypeF (TypeV "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (int,cz)
            [(annz,"f4",(TypeF (int) (int),cz),True)]
            (B.Var annz "$f4$(Int -> Int)$" (TypeF (int) (int),cz)
            (B.Match annz False
              (B.LVar "$f4$(Int -> Int)$")
              (B.Func annz (TypeF (int) (int),cz)
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "+")
                    (B.Tuple annz [B.Arg annz, B.Number annz 1]))))
                (B.Seq annz
                  (B.Nop annz)
                  (B.Inst annz "X" (bool,cz)
                    [(annz,"f4",(TypeF (bool) (int),cz),True)]
                    (B.Var annz "$f4$(Bool -> Int)$" (TypeF (bool) (int),cz)
                    (B.Match annz False
                      (B.LVar "$f4$(Bool -> Int)$")
                      (B.Func annz (TypeF (bool) (int),cz)
                        (B.Ret annz (B.Number annz 0)))
                      (B.Seq annz
                        (B.Nop annz)
                        (B.Ret annz (B.Call annz (B.Read annz "f4") (B.Number annz 1)))
                      )
                      (B.Nop annz))))
                )
                (B.Nop annz)))))))))
        `shouldBe` (Number 2)

    describe "misc" $ do

      evalProgItSuccess (Number 11)
        (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (B.Match annz False (B.LVar "a") (B.Number annz 1)
          (B.Ret annz (B.Call annz (B.Read annz "+") (B.Tuple annz [(B.Read annz "a"),(B.Number annz 10)])))
          (B.Ret annz (B.Error annz 99)))))

      evalProgItSuccess (Number 11)
        (B.Var annz "+" (TypeF (TypeN [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (B.Match annz False (B.LVar "a") (B.Number annz 1)
          (B.Var annz "b" (int,cz)
            (B.Match annz False (B.LVar "b") (B.Number annz 91)
              (B.Ret annz
                (B.Call annz (B.Read annz "+")
                             (B.Tuple annz [(B.Read annz "a"),(B.Number annz 10)])))
              (B.Ret annz (B.Error annz 92))))
          (B.Ret annz (B.Error annz 93)))))

      evalProgItSuccess (Number 1)
        (B.Ret annz (B.Number annz 1) `B.sSeq`
            B.Var annz "_" (int,cz) (B.Ret annz (B.Number annz 2)) `B.sSeq`
            B.Nop annz)

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
