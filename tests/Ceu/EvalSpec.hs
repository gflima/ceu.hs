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

int  = TData ["Int"]  [] TUnit
bool = TData ["Bool"] [] TUnit

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

  describe "Env/Envs" $ do

      it "pass: 1st write" $
        envWrite [("x",Nothing)] "x" (Cons ["Int","0"]) `shouldBe` [("x",Just (Cons ["Int","0"]))]

      it "pass: 2nd write" $
        envWrite [("x",Just (Cons ["Int","99"]))] "x" (Cons ["Int","0"]) `shouldBe` [("x",Just (Cons ["Int","0"]))]

      it "pass: write in middle" $
        envWrite [("a",Nothing),("x",Just (Cons ["Int","99"])),("b",Nothing)] "x" (Cons ["Int","0"]) `shouldBe` [("a",Nothing),("x",Just (Cons ["Int","0"])),("b",Nothing)]

      it "pass: write in last" $
        envWrite [("a",Nothing),("b",Nothing),("x",Just (Cons ["Int","99"]))] "x" (Cons ["Int","0"]) `shouldBe` [("a",Nothing),("b",Nothing),("x",Just (Cons ["Int","0"]))]

  describe "envRead vars id" $ do
      it "pass: read in simple env" $
        envRead [("x",Just (Cons ["Int","0"]))] "x" `shouldBe` (Cons ["Int","0"])

      it "pass: read in complex env" $
        let vars = [("y",Just (Cons ["Int","0"])),("x",Just (Cons ["Int","1"])),("z",Just (Cons ["Int","0"]))] in
          envRead vars "x" `shouldBe` (Cons ["Int","1"])

  describe "envEval vars exp" $ do
      it "pass: vars == [] && exp == (Number _)" $
        envEval [] (Cons ["Int","0"]) `shouldBe` (Cons ["Int","0"])

      it "pass: eval in simple env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("x",Just (Cons' ["Int","1"] Unit)),("y",Just (Cons' ["Int","2"] Unit))] in
          envEval vars (Call (Read "+") (Tuple [(Call (Read "-") (Tuple [(Read "x"),(Cons' ["Int","3"] Unit)])),(Call (Read "negate") (Read "y"))]))
          `shouldBe` (Cons' ["Int","-4"] Unit)

      it "pass: eval in complex env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("y",Just (Cons' ["Int","2"] Unit)),("x",Just (Cons' ["Int","1"] Unit)),
                    ("y",Just (Cons' ["Int","99"] Unit)),("x",Just (Cons' ["Int","99"] Unit))] in
          envEval vars (Call (Read "+") (Tuple [(Call (Read "-") (Tuple [(Read "x"),(Cons' ["Int","3"] Unit)])),(Call (Read "negate") (Read "y"))]))
          `shouldBe` (Cons' ["Int","-4"] Unit)

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (Match (LVar "x") (Cons ["Int","1"]) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (Cons ["Int","1"]))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (Cons ["Int","1"]))) (Match (LVar "x") (Cons ["Int","2"]) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (Cons ["Int","2"]))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (Match (LVar "x") (Cons ["Int","1"]) Nop Nop)), [])
        `shouldBe`
        (Var ("x",Nothing)
          (Match (LVar "x") (Cons ["Int","1"]) Nop Nop), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("+",Nothing)
          (Var ("x",(Just (Cons' ["Int","1"] Unit)))
          (Var ("y",Nothing)
          (Match (LVar "y") (Call (Read "+") (Tuple [(Read "x"),(Cons' ["Int","2"] Unit)])) Nop Nop)))), [])
        `shouldBe` (Var ("+",Nothing) (Var ("x",(Just (Cons' ["Int","1"] Unit))) (Var ("y",(Just (Cons' ["Int","3"] Unit))) Nop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (Var ("+",Nothing)
        (Var ("x",(Just (Cons' ["Int","1"] Unit)))
        (Var ("y",Nothing)
          (Match (LVar "y") (Call (Read "+") (Tuple [(Read "x"),(Cons' ["Int","2"] Unit)])) Nop Nop))), [])
        `shouldBe`
        (Var ("+",Nothing)
        (Var ("x",(Just (Cons' ["Int","1"] Unit)))
        (Var ("y",(Just (Cons' ["Int","3"] Unit))) Nop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (Cons' ["Int","0"] Unit)))
          (Match (LVar "x") (Call (Read "negate") (Call (Read "+") (Tuple [(Cons' ["Int","5"] Unit),(Cons' ["Int","1"] Unit)]))) Nop Nop))), [])
        `shouldBe`
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (Cons' ["Int","-6"] Unit))) Nop)), [])

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
        step (If (Read "x") Nop Nop, [("x",Just (Cons ["Int","0"]))])
        `shouldBe` (Nop, [("x",Just (Cons ["Int","0"]))])
      it "x /= 0" $
        step (If (Read "x") Nop Nop, [("x",Just (Cons ["Int","1"]))])
        `shouldBe` (Nop, [("x",Just (Cons ["Int","1"]))])
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
        (Var ("f", Just $ Func (Ret (Cons' ["Int","1"] Unit)))
        (Ret (Call (Read "f") Unit)))
        , [("_steps",Just $ Cons' ["Int","0"] Unit)])
      `shouldBe` (Cons' ["Int","1"] Unit)

    it "ret f(1)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+") (Tuple [Read "_arg",Cons' ["Int","1"] Unit]))))
        (Ret (Call (Read "f") (Cons' ["Int","2"] Unit)))))
        , [("_steps",Just $ Cons' ["Int","0"] Unit)])
      `shouldBe` (Cons' ["Int","3"] Unit)

    it "ret f(1,2)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ Func (Ret (Call (Read "+") (Read "_arg"))))
        (Ret (Call (Read "f") (Tuple [Cons' ["Int","1"] Unit,Cons' ["Int","2"] Unit])))))
        , [("_steps",Just $ Cons' ["Int","0"] Unit)])
      `shouldBe` (Cons' ["Int","3"] Unit)

  --------------------------------------------------------------------------
  describe "go" $ do

    describe "write" $ do

      it "(a,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TTop,cz)
          (B.Var annz "b" (TTop,cz)
          (B.Match annz False (B.LTuple [B.LVar "a",B.LVar "b"]) (B.Tuple annz [B.Cons annz ["Int","1"],B.Cons annz ["Int","2"]])
            (B.Ret annz (B.Read annz "b"))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Cons' ["Int","2"] Unit)

      it "(_,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TTop,cz)
          (B.Var annz "b" (TTop,cz)
          (B.Match annz False (B.LTuple [B.LAny,B.LVar "b"]) (B.Tuple annz [B.Cons annz ["Int","1"],B.Cons annz ["Int","2"]])
            (B.Ret annz (B.Read annz "b"))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Cons' ["Int","2"] Unit)

      it "1 <- 1" $
        go
          (B.Data annz (int,cz) False
          (B.Match annz False (B.LCons ["Int","1"] B.LUnit) (B.Cons annz ["Int","1"])
            (B.Ret annz (B.Cons annz ["Int","2"]))
            (B.Ret annz (B.Error annz 99))))
          `shouldBe` (Cons' ["Int","2"] Unit)

      it "a <- 1 ; `a` <- 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","1"])
            (B.Match annz True (B.LExp $ B.Read annz "a") (B.Cons annz ["Int","1"])
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 99)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Cons' ["Int","1"] Unit)

      it "a <- 2 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","2"])
            (B.Match annz True (B.LCons ["Int","1"] B.LUnit) (B.Read annz "a")
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 10)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Error 10)

      it "a <- 1 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","1"])
            (B.Match annz True (B.LCons ["Int","1"] B.LUnit) (B.Read annz "a")
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 99)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Cons' ["Int","1"] Unit)

      it "a <- 1 ; `a` <- 2" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","1"])
            (B.Match annz True (B.LExp $ B.Read annz "a") (B.Cons annz ["Int","2"])
              (B.Ret   annz (B.Read annz "a"))
              (B.Ret   annz (B.Error annz 10)))
            (B.Ret   annz (B.Error annz 99)))))
        `shouldBe` (Error 10)

    describe "func" $ do

      it "Int ; f1 ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit (int),cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TFunc TUnit (int),cz)
                          (B.Ret annz (B.Cons annz ["Int","1"])))
            (B.Ret annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
            (B.Ret annz (B.Error annz 99)))))
        `shouldBe` (Cons' ["Int","1"] Unit)

      it "Int ; f1 (err!) ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit TUnit,cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TFunc TUnit TUnit,cz)
                          (B.Ret annz (B.Error annz 1)))
            (B.Ret annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
            (B.Ret annz (B.Error annz 99)))))
        `shouldBe` (Error 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit TUnit,cz)
          (B.Match annz False (B.LVar "f1")
                        (B.Func annz (TFunc TUnit TUnit,cz)
                          (B.Ret annz (B.Error annz 1)))
            (B.Seq annz
              (B.CallS annz (B.Call annz (B.Read annz "f1") (B.Unit annz)))
              (B.Ret annz (B.Cons annz ["Int","99"])))
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
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Var annz "c" (TFunc (int) (int),cz)
          (B.Match annz False (B.LVar "c")
                        (B.Func annz (TFunc (int) (int),cz)
                          (B.Ret annz (B.Arg annz)))
            (B.Var annz "f" (TFunc (TTuple [int, int]) (int),cz)
              (B.Var annz "g" (TFunc (int) (int),cz)
              (B.Match annz False (B.LTuple [B.LVar "f",B.LVar "g"]) (B.Tuple annz [B.Read annz "+",B.Read annz "c"])
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "f")
                    (B.Tuple annz [
                      B.Call annz (B.Read annz "c") (B.Cons annz ["Int","1"]),
                      B.Call annz (B.Read annz "c") (B.Cons annz ["Int","2"])])))
                (B.Ret annz (B.Error annz 99)))))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Cons' ["Int","3"] Unit)

      it "glb <- 1 ; f () -> glb ; ret glb" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (B.Match annz False (B.LVar "glb") (B.Cons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (int),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TFunc TUnit (int),cz)
                              (B.Ret annz (B.Read annz "glb")))
                (B.Ret annz
                  (B.Call annz (B.Read annz "f") (B.Unit annz)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99)))))
          `shouldBe` (Cons' ["Int","1"] Unit)

      it "glb <- 1 ; f() -> g() -> glb ; ret f()()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (B.Match annz False (B.LVar "glb") (B.Cons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (TFunc TUnit (int)),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TFunc TUnit (TFunc TUnit (int)),cz)
                              (B.Ret annz
                                (B.Func annz (TFunc TUnit (int),cz)
                                  (B.Ret annz (B.Read annz "glb")))))
                (B.Ret annz
                  (B.Call annz
                    (B.Call annz (B.Read annz "f") (B.Unit annz))
                    (B.Unit annz)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99)))))
          `shouldBe` (Cons' ["Int","1"] Unit)

      it "(TODO: loc lifetime) g' <- nil ; { loc <- 1 ; f() -> g() -> glb ; g' <- f() } ; ret g'()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "g'" (TFunc TUnit (int),cz)
          (B.Var   annz "loc" (int,cz)
          (B.Match annz False (B.LVar "loc") (B.Cons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (TFunc TUnit (int)),cz)
              (B.Match annz False (B.LVar "f")
                            (B.Func annz (TFunc TUnit (TFunc TUnit (int)),cz)
                              (B.Ret annz
                                (B.Func annz (TFunc TUnit (int),cz)
                                  (B.Ret annz (B.Read annz "loc")))))
                (B.Match annz False (B.LVar "g'")
                              (B.Call annz (B.Read annz "f") (B.Unit annz))
                  (B.Ret annz
                    (B.Call annz (B.Read annz "g'") (B.Unit annz)))
                  (B.Ret annz (B.Error annz 99)))
                (B.Ret annz (B.Error annz 99))))
            (B.Ret annz (B.Error annz 99))))))
          `shouldBe` (Cons' ["Int","1"] Unit)

    describe "data" $ do

      it "data X with Int ; x <- X 1 ; return x" $
        go
          (B.Data annz (int,cz) False
          (B.Data annz (TData ["X"] [] int,cz) False
          (B.Var annz "x" (TData ["X"] [] (int),cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Cons annz ["Int","1"]))
            (B.Ret annz (B.Read annz "x"))
            (B.Ret annz (B.Error annz 99))))))
        `shouldBe` (Cons' ["X"] (Cons' ["Int","1"] Unit))

      it "data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (TData ["X"] [] (TTuple [int, int]),cz) False
          (B.Var annz "x" (TData ["X"] [] (TTuple [int, int]),cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Tuple annz [B.Call annz (B.Read annz "+") (B.Tuple annz [B.Cons annz ["Int","1"],B.Cons annz ["Int","2"]]), B.Cons annz ["Int","3"]]))
            (B.Ret annz (B.Read annz "x"))
            (B.Ret annz (B.Error annz 99)))))))
        `shouldBe` (Cons' ["X"] (Tuple [Cons' ["Int","3"] Unit,Cons' ["Int","3"] Unit]))

      it "TODO (coerse): data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (TData ["X"] [] (TTuple [int, int]),cz) False
          (B.Var annz "x" (TData ["X"] [] TUnit,cz)
          (B.Match annz False (B.LVar "x") (B.Call annz (B.Cons annz ["X"]) (B.Tuple annz [B.Cons annz ["Int","1"],B.Cons annz ["Int","2"]]))
            (B.Ret annz (B.Call annz (B.Read annz "+") (B.Read annz "x")))
            (B.Ret annz (B.Error annz 99)))))))
        `shouldBe` (Cons' ["X"] (Cons' ["Int","1"] Unit))

      it "data X with Int ; x:Int ; X x <- X 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Data  annz (TData ["X"] [] int,cz) False
          (B.Var   annz "x" (int,cz)
          (B.Match annz False (B.LCons ["X"] (B.LVar "x")) (B.Call annz (B.Cons annz ["X"]) (B.Cons annz ["Int","1"]))
            (B.Ret   annz (B.Read annz "x"))
            (B.Ret   annz (B.Error annz 99))))))
        `shouldBe` (Cons' ["Int","1"] Unit)

    describe "class" $ do

      it "Int ; X a ; inst X Int ; return f3 1" $
        go
          (B.Data annz (int,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f3",(TFunc (TAny "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f3" (TFunc (TAny "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (int,cz)
            [(annz,"f3",(TFunc (int) (int),cz),True)]
            (B.Var annz "$f3$(Int -> Int)$" (TFunc (int) (int),cz)
            (B.Match annz False
              (B.LVar "$f3$(Int -> Int)$")
              (B.Func annz (TFunc (int) (int),cz)
                (B.Ret annz (B.Cons annz ["Int","1"])))
              (B.Seq annz
                (B.Nop annz)
                (B.Ret annz (B.Call annz (B.Read annz "f3") (B.Cons annz ["Int","1"]))))
              (B.Nop annz)))))))
        `shouldBe` (Cons' ["Int","1"] Unit)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f2 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (bool,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f2",(TFunc (TAny "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f2" (TFunc (TAny "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (bool,cz)
            [(annz,"f2",(TFunc (bool) (int),cz),True)]
            (B.Var annz "$f2$(Bool -> Int)$" (TFunc (bool) (int),cz)
            (B.Match annz False
              (B.LVar "$f2$(Bool -> Int)$")
              (B.Func annz (TFunc (bool) (int),cz)
                (B.Ret annz (B.Cons annz ["Int","0"])))
              (B.Seq annz
                (B.Nop annz)
                (B.Inst annz "X" (int,cz)
                  [(annz,"f2",(TFunc (int) (int),cz),True)]
                  (B.Var annz "$f2$(Int -> Int)$" (TFunc (int) (int),cz)
                  (B.Match annz False
                    (B.LVar "$f2$(Int -> Int)$")
                    (B.Func annz (TFunc (int) (int),cz)
                      (B.Ret annz
                        (B.Call annz
                          (B.Read annz "+")
                          (B.Tuple annz [B.Arg annz, B.Cons annz ["Int","1"]]))))
                    (B.Seq annz
                      (B.Nop annz)
                      (B.Var annz "ret" (int,cz)
                      (B.Match annz False (B.LVar "ret")
                        (B.Call annz (B.Read annz "f2") (B.Cons annz ["Int","1"]))
                        (B.Ret annz (B.Read annz "ret"))
                        (B.Ret annz (B.Error annz 99))))
                    )
                    (B.Nop annz))))
                    )
                    (B.Nop annz)))))))))
        `shouldBe` (Cons' ["Int","2"] Unit)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f4 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (bool,cz) False
          (B.Class annz "X" (cv "a")
            [(annz,"f4",(TFunc (TAny "a") (int),cvc ("a","X")),False)]
          (B.Var annz "f4" (TFunc (TAny "a") (int),cvc ("a","X"))
          (B.Inst annz "X" (int,cz)
            [(annz,"f4",(TFunc (int) (int),cz),True)]
            (B.Var annz "$f4$(Int -> Int)$" (TFunc (int) (int),cz)
            (B.Match annz False
              (B.LVar "$f4$(Int -> Int)$")
              (B.Func annz (TFunc (int) (int),cz)
                (B.Ret annz
                  (B.Call annz
                    (B.Read annz "+")
                    (B.Tuple annz [B.Arg annz, B.Cons annz ["Int","1"]]))))
                (B.Seq annz
                  (B.Nop annz)
                  (B.Inst annz "X" (bool,cz)
                    [(annz,"f4",(TFunc (bool) (int),cz),True)]
                    (B.Var annz "$f4$(Bool -> Int)$" (TFunc (bool) (int),cz)
                    (B.Match annz False
                      (B.LVar "$f4$(Bool -> Int)$")
                      (B.Func annz (TFunc (bool) (int),cz)
                        (B.Ret annz (B.Cons annz ["Int","0"])))
                      (B.Seq annz
                        (B.Nop annz)
                        (B.Ret annz (B.Call annz (B.Read annz "f4") (B.Cons annz ["Int","1"])))
                      )
                      (B.Nop annz))))
                )
                (B.Nop annz)))))))))
        `shouldBe` (Cons' ["Int","2"] Unit)

    describe "misc" $ do

      evalProgItSuccess (Cons' ["Int","11"] Unit)
        (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","1"])
          (B.Ret annz (B.Call annz (B.Read annz "+") (B.Tuple annz [(B.Read annz "a"),(B.Cons annz ["Int","10"])])))
          (B.Ret annz (B.Error annz 99)))))

      evalProgItSuccess (Cons' ["Int","11"] Unit)
        (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (B.Match annz False (B.LVar "a") (B.Cons annz ["Int","1"])
          (B.Var annz "b" (int,cz)
            (B.Match annz False (B.LVar "b") (B.Cons annz ["Int","91"])
              (B.Ret annz
                (B.Call annz (B.Read annz "+")
                             (B.Tuple annz [(B.Read annz "a"),(B.Cons annz ["Int","10"])])))
              (B.Ret annz (B.Error annz 92))))
          (B.Ret annz (B.Error annz 93)))))

      evalProgItSuccess (Cons' ["Int","1"] Unit)
        (B.Ret annz (B.Cons annz ["Int","1"]) `B.sSeq`
            B.Var annz "_" (int,cz) (B.Ret annz (B.Cons annz ["Int","2"])) `B.sSeq`
            B.Nop annz)

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
