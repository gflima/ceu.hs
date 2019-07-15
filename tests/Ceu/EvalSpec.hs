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

mmm          loc exp p1 p2 =   Match         exp [(  Nop,  loc,p1)]
mmmAny z     loc exp p1 p2 = B.Match z False exp [(B.Nop z,loc,p1),(B.Nop z,B.EAny z,p2)]
mmmOne z chk loc exp p1 p2 = B.Match z chk   exp [(B.Nop z,loc,p1)]

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  --describe "TODO" $ do

  describe "Env/Envs" $ do

      it "pass: 1st write" $
        envWrite [("x",Nothing)] "x" (ECons ["Int","0"]) `shouldBe` [("x",Just (ECons ["Int","0"]))]

      it "pass: 2nd write" $
        envWrite [("x",Just (ECons ["Int","99"]))] "x" (ECons ["Int","0"]) `shouldBe` [("x",Just (ECons ["Int","0"]))]

      it "pass: write in middle" $
        envWrite [("a",Nothing),("x",Just (ECons ["Int","99"])),("b",Nothing)] "x" (ECons ["Int","0"]) `shouldBe` [("a",Nothing),("x",Just (ECons ["Int","0"])),("b",Nothing)]

      it "pass: write in last" $
        envWrite [("a",Nothing),("b",Nothing),("x",Just (ECons ["Int","99"]))] "x" (ECons ["Int","0"]) `shouldBe` [("a",Nothing),("b",Nothing),("x",Just (ECons ["Int","0"]))]

  describe "envRead vars id" $ do
      it "pass: read in simple env" $
        envRead [("x",Just (ECons ["Int","0"]))] "x" `shouldBe` (ECons ["Int","0"])

      it "pass: read in complex env" $
        let vars = [("y",Just (ECons ["Int","0"])),("x",Just (ECons ["Int","1"])),("z",Just (ECons ["Int","0"]))] in
          envRead vars "x" `shouldBe` (ECons ["Int","1"])

  describe "envEval vars exp" $ do
      it "pass: vars == [] && exp == (Number _)" $
        envEval [] (ECons ["Int","0"]) `shouldBe` (ECons ["Int","0"])

      it "pass: eval in simple env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("x",Just (EData ["Int","1"] EUnit)),("y",Just (EData ["Int","2"] EUnit))] in
          envEval vars (ECall (EVar "+") (ETuple [(ECall (EVar "-") (ETuple [(EVar "x"),(EData ["Int","3"] EUnit)])),(ECall (EVar "negate") (EVar "y"))]))
          `shouldBe` (EData ["Int","-4"] EUnit)

      it "pass: eval in complex env" $
        let vars = [("negate",Nothing), ("+",Nothing), ("-",Nothing),
                    ("y",Just (EData ["Int","2"] EUnit)),("x",Just (EData ["Int","1"] EUnit)),
                    ("y",Just (EData ["Int","99"] EUnit)),("x",Just (EData ["Int","99"] EUnit))] in
          envEval vars (ECall (EVar "+") (ETuple [(ECall (EVar "-") (ETuple [(EVar "x"),(EData ["Int","3"] EUnit)])),(ECall (EVar "negate") (EVar "y"))]))
          `shouldBe` (EData ["Int","-4"] EUnit)

  --------------------------------------------------------------------------
  describe "step" $ do

    -- write --
    describe "write" $ do
      it "[x=?] x=1" $
        step (Var ("x",Nothing) (mmm (EVar "x") (ECons ["Int","1"]) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (ECons ["Int","1"]))) Nop, [])

      it "[x=1] x=2" $
        step (Var ("x",(Just (EData ["Int","1"] EUnit))) (mmm (EVar "x") (EData ["Int","2"] EUnit) Nop Nop), [])
        `shouldBe` (Var ("x",(Just (EData ["Int","2"] EUnit))) Nop, [])

      it "nop; x=1" $
        step
        (Var ("x",Nothing)
          (Nop `Seq` (mmm (EVar "x") (ECons ["Int","1"]) Nop Nop)), [])
        `shouldBe`
        (Var ("x",Nothing)
          (mmm (EVar "x") (ECons ["Int","1"]) Nop Nop), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (Var ("+",Nothing)
          (Var ("x",(Just (EData ["Int","1"] EUnit)))
          (Var ("y",Nothing)
          (mmm (EVar "y") (ECall (EVar "+") (ETuple [(EVar "x"),(EData ["Int","2"] EUnit)])) Nop Nop)))), [])
        `shouldBe` (Var ("+",Nothing) (Var ("x",(Just (EData ["Int","1"] EUnit))) (Var ("y",(Just (EData ["Int","3"] EUnit))) Nop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (Var ("+",Nothing)
        (Var ("x",(Just (EData ["Int","1"] EUnit)))
        (Var ("y",Nothing)
          (mmm (EVar "y") (ECall (EVar "+") (ETuple [(EVar "x"),(EData ["Int","2"] EUnit)])) Nop Nop))), [])
        `shouldBe`
        (Var ("+",Nothing)
        (Var ("x",(Just (EData ["Int","1"] EUnit)))
        (Var ("y",(Just (EData ["Int","3"] EUnit))) Nop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (EData ["Int","0"] EUnit)))
          (mmm (EVar "x") (ECall (EVar "negate") (ECall (EVar "+") (ETuple [(EData ["Int","5"] EUnit),(EData ["Int","1"] EUnit)]))) Nop Nop))), [])
        `shouldBe`
        (Var ("negate",Nothing)
        (Var ("+",Nothing)
        (Var ("x",(Just (EData ["Int","-6"] EUnit))) Nop)), [])

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
        step (If (EVar "x") Nop Nop, [("x",Just (ECons ["Int","0"]))])
        `shouldBe` (Nop, [("x",Just (ECons ["Int","0"]))])
      it "x /= 0" $
        step (If (EVar "x") Nop Nop, [("x",Just (ECons ["Int","1"]))])
        `shouldBe` (Nop, [("x",Just (ECons ["Int","1"]))])
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
        (Var ("f", Just $ EFunc (Ret (EData ["Int","1"] EUnit)))
        (Ret (ECall (EVar "f") EUnit)))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","1"] EUnit)

    it "ret f(1)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ EFunc (Ret (ECall (EVar "+") (ETuple [EVar "_arg",EData ["Int","1"] EUnit]))))
        (Ret (ECall (EVar "f") (EData ["Int","2"] EUnit)))))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","3"] EUnit)

    it "ret f(1,2)" $
      steps (
        (Var ("+", Nothing)
        (Var ("f", Just $ EFunc (Ret (ECall (EVar "+") (EVar "_arg"))))
        (Ret (ECall (EVar "f") (ETuple [EData ["Int","1"] EUnit,EData ["Int","2"] EUnit])))))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","3"] EUnit)

  --------------------------------------------------------------------------
  describe "go" $ do

    describe "write" $ do

      it "(a,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TTop,cz)
          (B.Var annz "b" (TTop,cz)
          (mmmOne annz False (B.ETuple annz [B.EVar annz "a",B.EVar annz "b"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]])
            (B.Ret annz (B.EVar annz "b"))
            (B.Ret annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "(_,b) <- (1,2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "a" (TTop,cz)
          (B.Var annz "b" (TTop,cz)
          (mmmOne annz False (B.ETuple annz [B.EAny annz,B.EVar annz "b"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]])
            (B.Ret annz (B.EVar annz "b"))
            (B.Ret annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "1 <- 1" $
        go
          (B.Data annz (int,cz) False
          (mmmOne annz False (B.ECons annz ["Int","1"]) (B.ECons annz ["Int","1"])
            (B.Ret annz (B.ECons annz ["Int","2"]))
            (B.Ret annz (B.EError annz 99))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "a <- 1 ; `a` <- 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.EExp annz $ B.EVar annz "a") (B.ECons annz ["Int","1"])
              (B.Ret   annz (B.EVar annz "a"))
              (B.Ret   annz (B.EError annz 99)))
            (B.Ret   annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "a <- 2 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","2"])
            (mmmAny annz (B.ECons annz ["Int","1"]) (B.EVar annz "a")
              (B.Ret   annz (B.EVar annz "a"))
              (B.Ret   annz (B.EError annz 10)))
            (B.Ret   annz (B.EError annz 99)))))
        `shouldBe` (EError 10)

      it "a <- 1 ; 1 <- a" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.ECons annz ["Int","1"]) (B.EVar annz "a")
              (B.Ret   annz (B.EVar annz "a"))
              (B.Ret   annz (B.EError annz 99)))
            (B.Ret   annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "a <- 1 ; `a` <- 2" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.EExp annz $ B.EVar annz "a") (B.ECons annz ["Int","2"])
              (B.Ret   annz (B.EVar annz "a"))
              (B.Ret   annz (B.EError annz 10)))
            (B.Ret   annz (B.EError annz 99)))))
        `shouldBe` (EError 10)

    describe "func" $ do

      it "Int ; f1 ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit (int),cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz (TFunc TUnit (int),cz)
                          (B.Ret annz (B.ECons annz ["Int","1"])))
            (B.Ret annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
            (B.Ret annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "Int ; f1 (err!) ; return f1 1" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit TUnit,cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz (TFunc TUnit TUnit,cz)
                          (B.Ret annz (B.EError annz 1)))
            (B.Ret annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
            (B.Ret annz (B.EError annz 99)))))
        `shouldBe` (EError 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "f1" (TFunc TUnit TUnit,cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz (TFunc TUnit TUnit,cz)
                          (B.Ret annz (B.EError annz 1)))
            (B.Seq annz
              (B.CallS annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
              (B.Ret annz (B.ECons annz ["Int","99"])))
            (B.Ret annz (B.EError annz 99)))))
        `shouldBe` (EError 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.Seq annz
            (B.CallS annz (B.ECall annz (B.EError annz 1) (B.EUnit annz)))
            (B.Ret annz (B.EError annz 99)))
        `shouldBe` (EError 1)

      it "(f,g) <- (+,c) ; return f(g 1, g 2)" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Var annz "c" (TFunc (int) (int),cz)
          (mmmOne annz False (B.EVar annz "c")
                        (B.EFunc annz (TFunc (int) (int),cz)
                          (B.Ret annz (B.EArg annz)))
            (B.Var annz "f" (TFunc (TTuple [int, int]) (int),cz)
              (B.Var annz "g" (TFunc (int) (int),cz)
              (mmmOne annz False (B.ETuple annz [B.EVar annz "f",B.EVar annz "g"]) (B.ETuple annz [B.EVar annz "+",B.EVar annz "c"])
                (B.Ret annz
                  (B.ECall annz
                    (B.EVar annz "f")
                    (B.ETuple annz [
                      B.ECall annz (B.EVar annz "c") (B.ECons annz ["Int","1"]),
                      B.ECall annz (B.EVar annz "c") (B.ECons annz ["Int","2"])])))
                (B.Ret annz (B.EError annz 99)))))
            (B.Ret annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","3"] EUnit)

      it "glb <- 1 ; f () -> glb ; ret glb" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (mmmOne annz False (B.EVar annz "glb") (B.ECons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (int),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz (TFunc TUnit (int),cz)
                              (B.Ret annz (B.EVar annz "glb")))
                (B.Ret annz
                  (B.ECall annz (B.EVar annz "f") (B.EUnit annz)))
                (B.Ret annz (B.EError annz 99))))
            (B.Ret annz (B.EError annz 99)))))
          `shouldBe` (EData ["Int","1"] EUnit)

      it "glb <- 1 ; f() -> g() -> glb ; ret f()()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "glb" (int,cz)
          (mmmOne annz False (B.EVar annz "glb") (B.ECons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (TFunc TUnit (int)),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz (TFunc TUnit (TFunc TUnit (int)),cz)
                              (B.Ret annz
                                (B.EFunc annz (TFunc TUnit (int),cz)
                                  (B.Ret annz (B.EVar annz "glb")))))
                (B.Ret annz
                  (B.ECall annz
                    (B.ECall annz (B.EVar annz "f") (B.EUnit annz))
                    (B.EUnit annz)))
                (B.Ret annz (B.EError annz 99))))
            (B.Ret annz (B.EError annz 99)))))
          `shouldBe` (EData ["Int","1"] EUnit)

      it "(TODO: loc lifetime) g' <- nil ; { loc <- 1 ; f() -> g() -> glb ; g' <- f() } ; ret g'()" $
        go
          (B.Data  annz (int,cz) False
          (B.Var   annz "g'" (TFunc TUnit (int),cz)
          (B.Var   annz "loc" (int,cz)
          (mmmOne annz False (B.EVar annz "loc") (B.ECons annz ["Int","1"])
            (B.Var   annz "f" (TFunc TUnit (TFunc TUnit (int)),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz (TFunc TUnit (TFunc TUnit (int)),cz)
                              (B.Ret annz
                                (B.EFunc annz (TFunc TUnit (int),cz)
                                  (B.Ret annz (B.EVar annz "loc")))))
                (mmmOne annz False (B.EVar annz "g'")
                              (B.ECall annz (B.EVar annz "f") (B.EUnit annz))
                  (B.Ret annz
                    (B.ECall annz (B.EVar annz "g'") (B.EUnit annz)))
                  (B.Ret annz (B.EError annz 99)))
                (B.Ret annz (B.EError annz 99))))
            (B.Ret annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","1"] EUnit)

    describe "data" $ do

      it "data X with Int ; x <- X 1 ; return x" $
        go
          (B.Data annz (int,cz) False
          (B.Data annz (TData ["X"] [] int,cz) False
          (B.Var annz "x" (TData ["X"] [] (int),cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ECons annz ["Int","1"]))
            (B.Ret annz (B.EVar annz "x"))
            (B.Ret annz (B.EError annz 99))))))
        `shouldBe` (EData ["X"] (EData ["Int","1"] EUnit))

      it "data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (TData ["X"] [] (TTuple [int, int]),cz) False
          (B.Var annz "x" (TData ["X"] [] (TTuple [int, int]),cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ETuple annz [B.ECall annz (B.EVar annz "+") (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]]), B.ECons annz ["Int","3"]]))
            (B.Ret annz (B.EVar annz "x"))
            (B.Ret annz (B.EError annz 99)))))))
        `shouldBe` (EData ["X"] (ETuple [EData ["Int","3"] EUnit,EData ["Int","3"] EUnit]))

      it "TODO (coerse): data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.Data annz (int,cz) False
          (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
          (B.Data annz (TData ["X"] [] (TTuple [int, int]),cz) False
          (B.Var annz "x" (TData ["X"] [] TUnit,cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]]))
            (B.Ret annz (B.ECall annz (B.EVar annz "+") (B.EVar annz "x")))
            (B.Ret annz (B.EError annz 99)))))))
        `shouldBe` (EData ["X"] (EData ["Int","1"] EUnit))

      it "data X with Int ; x:Int ; X x <- X 1" $
        go
          (B.Data  annz (int,cz) False
          (B.Data  annz (TData ["X"] [] int,cz) False
          (B.Var   annz "x" (int,cz)
          (mmmOne annz False (B.ECall annz (B.ECons annz ["X"]) (B.EVar annz "x")) (B.ECall annz (B.ECons annz ["X"]) (B.ECons annz ["Int","1"]))
            (B.Ret   annz (B.EVar annz "x"))
            (B.Ret   annz (B.EError annz 99))))))
        `shouldBe` (EData ["Int","1"] EUnit)

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
            (mmmOne annz False
              (B.EVar annz "$f3$(Int -> Int)$")
              (B.EFunc annz (TFunc (int) (int),cz)
                (B.Ret annz (B.ECons annz ["Int","1"])))
              (B.Seq annz
                (B.Nop annz)
                (B.Ret annz (B.ECall annz (B.EVar annz "f3") (B.ECons annz ["Int","1"]))))
              (B.Nop annz)))))))
        `shouldBe` (EData ["Int","1"] EUnit)

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
            (mmmOne annz False
              (B.EVar annz "$f2$(Bool -> Int)$")
              (B.EFunc annz (TFunc (bool) (int),cz)
                (B.Ret annz (B.ECons annz ["Int","0"])))
              (B.Seq annz
                (B.Nop annz)
                (B.Inst annz "X" (int,cz)
                  [(annz,"f2",(TFunc (int) (int),cz),True)]
                  (B.Var annz "$f2$(Int -> Int)$" (TFunc (int) (int),cz)
                  (mmmOne annz False
                    (B.EVar annz "$f2$(Int -> Int)$")
                    (B.EFunc annz (TFunc (int) (int),cz)
                      (B.Ret annz
                        (B.ECall annz
                          (B.EVar annz "+")
                          (B.ETuple annz [B.EArg annz, B.ECons annz ["Int","1"]]))))
                    (B.Seq annz
                      (B.Nop annz)
                      (B.Var annz "ret" (int,cz)
                      (mmmOne annz False (B.EVar annz "ret")
                        (B.ECall annz (B.EVar annz "f2") (B.ECons annz ["Int","1"]))
                        (B.Ret annz (B.EVar annz "ret"))
                        (B.Ret annz (B.EError annz 99))))
                    )
                    (B.Nop annz))))
                    )
                    (B.Nop annz)))))))))
        `shouldBe` (EData ["Int","2"] EUnit)

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
            (mmmOne annz False
              (B.EVar annz "$f4$(Int -> Int)$")
              (B.EFunc annz (TFunc (int) (int),cz)
                (B.Ret annz
                  (B.ECall annz
                    (B.EVar annz "+")
                    (B.ETuple annz [B.EArg annz, B.ECons annz ["Int","1"]]))))
                (B.Seq annz
                  (B.Nop annz)
                  (B.Inst annz "X" (bool,cz)
                    [(annz,"f4",(TFunc (bool) (int),cz),True)]
                    (B.Var annz "$f4$(Bool -> Int)$" (TFunc (bool) (int),cz)
                    (mmmOne annz False
                      (B.EVar annz "$f4$(Bool -> Int)$")
                      (B.EFunc annz (TFunc (bool) (int),cz)
                        (B.Ret annz (B.ECons annz ["Int","0"])))
                      (B.Seq annz
                        (B.Nop annz)
                        (B.Ret annz (B.ECall annz (B.EVar annz "f4") (B.ECons annz ["Int","1"])))
                      )
                      (B.Nop annz))))
                )
                (B.Nop annz)))))))))
        `shouldBe` (EData ["Int","2"] EUnit)

    describe "misc" $ do

      evalProgItSuccess (EData ["Int","11"] EUnit)
        (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
          (B.Ret annz (B.ECall annz (B.EVar annz "+") (B.ETuple annz [(B.EVar annz "a"),(B.ECons annz ["Int","10"])])))
          (B.Ret annz (B.EError annz 99)))))

      evalProgItSuccess (EData ["Int","11"] EUnit)
        (B.Var annz "+" (TFunc (TTuple [int, int]) (int),cz)
        (B.Var annz "a" (int,cz)
        (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
          (B.Var annz "b" (int,cz)
            (mmmOne annz False (B.EVar annz "b") (B.ECons annz ["Int","91"])
              (B.Ret annz
                (B.ECall annz (B.EVar annz "+")
                             (B.ETuple annz [(B.EVar annz "a"),(B.ECons annz ["Int","10"])])))
              (B.Ret annz (B.EError annz 92))))
          (B.Ret annz (B.EError annz 93)))))

      evalProgItSuccess (EData ["Int","1"] EUnit)
        (B.Ret annz (B.ECons annz ["Int","1"]) `B.sSeq`
            B.Var annz "_" (int,cz) (B.Ret annz (B.ECons annz ["Int","2"])) `B.sSeq`
            B.Nop annz)

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
