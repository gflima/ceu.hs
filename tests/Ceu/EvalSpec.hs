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

int  = TData False ["Int"]  [] (TUnit False)
bool = TData False ["Bool"] [] (TUnit False)

mmm          loc exp p1 p2 =   SMatch         exp [(  SNop,  loc,p1)]
mmmAny z     loc exp p1 p2 = B.SMatch z False exp [(B.SNop z,loc,p1),(B.SNop z,B.EAny z,p2)]
mmmOne z chk loc exp p1 p2 = B.SMatch z chk   exp [(B.SNop z,loc,p1)]

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
        step (SVar ("x",Nothing) (mmm (EVar "x") (ECons ["Int","1"]) SNop SNop), [])
        `shouldBe` (SVar ("x",(Just (ECons ["Int","1"]))) SNop, [])

      it "[x=1] x=2" $
        step (SVar ("x",(Just (EData ["Int","1"] EUnit))) (mmm (EVar "x") (EData ["Int","2"] EUnit) SNop SNop), [])
        `shouldBe` (SVar ("x",(Just (EData ["Int","2"] EUnit))) SNop, [])

      it "nop; x=1" $
        step
        (SVar ("x",Nothing)
          (SNop `SSeq` (mmm (EVar "x") (ECons ["Int","1"]) SNop SNop)), [])
        `shouldBe`
        (SVar ("x",Nothing)
          (mmm (EVar "x") (ECons ["Int","1"]) SNop SNop), [])

      it "[x=1,y=?] y=x+2" $
        step (
          (SVar ("+",Nothing)
          (SVar ("x",(Just (EData ["Int","1"] EUnit)))
          (SVar ("y",Nothing)
          (mmm (EVar "y") (ECall (EVar "+") (ETuple [(EVar "x"),(EData ["Int","2"] EUnit)])) SNop SNop)))), [])
        `shouldBe` (SVar ("+",Nothing) (SVar ("x",(Just (EData ["Int","1"] EUnit))) (SVar ("y",(Just (EData ["Int","3"] EUnit))) SNop)), [])

      it "[x=1,y=?] y=x+2" $
        step
          (SVar ("+",Nothing)
        (SVar ("x",(Just (EData ["Int","1"] EUnit)))
        (SVar ("y",Nothing)
          (mmm (EVar "y") (ECall (EVar "+") (ETuple [(EVar "x"),(EData ["Int","2"] EUnit)])) SNop SNop))), [])
        `shouldBe`
        (SVar ("+",Nothing)
        (SVar ("x",(Just (EData ["Int","1"] EUnit)))
        (SVar ("y",(Just (EData ["Int","3"] EUnit))) SNop)), [])

      it "[x=?] x=-(5+1)" $
        step
        (SVar ("negate",Nothing)
        (SVar ("+",Nothing)
        (SVar ("x",(Just (EData ["Int","0"] EUnit)))
          (mmm (EVar "x") (ECall (EVar "negate") (ECall (EVar "+") (ETuple [(EData ["Int","5"] EUnit),(EData ["Int","1"] EUnit)]))) SNop SNop))), [])
        `shouldBe`
        (SVar ("negate",Nothing)
        (SVar ("+",Nothing)
        (SVar ("x",(Just (EData ["Int","-6"] EUnit))) SNop)), [])

  describe "seq" $ do
      it "nop" $
        step (SSeq SNop SNop, [])
        `shouldBe` (SNop, [])
      it "adv" $
        step (SSeq (SSeq SNop SNop) SNop, [])
        `shouldBe` (SSeq SNop SNop, [])

{-
  describe "if" $ do
      it "x == 0" $
        step (SIf (EVar "x") SNop SNop, [("x",Just (ECons ["Int","0"]))])
        `shouldBe` (SNop, [("x",Just (ECons ["Int","0"]))])
      it "x /= 0" $
        step (SIf (EVar "x") SNop SNop, [("x",Just (ECons ["Int","1"]))])
        `shouldBe` (SNop, [("x",Just (ECons ["Int","1"]))])
-}

  describe "loop" $ do
      it "nop" $
        step (SLoop' SNop SNop, [])
        `shouldBe` (SLoop' SNop SNop, [])
{-
  describe "(SLoop' (Escape 0) q)" $ do
      it "pass: lvl == 0" $
        step (SLoop' (Escape 0) SNop, [])
        `shouldBe` (Escape 0, [])

      it "pass: lvl > 0" $
        step (SLoop' (Escape 0) (SSeq (EmitEvt "z") SNop), [])
        `shouldBe` ((Escape 0), [])
-}
      it "adv" $
        step (SLoop' (SSeq SNop SNop) SNop, [])
        `shouldBe` (SLoop' SNop SNop, [])

  describe "func" $ do
    it "ret f()" $
      steps (
        (SVar ("f", Just $ EFunc (SRet (EData ["Int","1"] EUnit)))
        (SRet (ECall (EVar "f") EUnit)))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","1"] EUnit)

    it "ret f(1)" $
      steps (
        (SVar ("+", Nothing)
        (SVar ("f", Just $ EFunc (SRet (ECall (EVar "+") (ETuple [EVar "_arg",EData ["Int","1"] EUnit]))))
        (SRet (ECall (EVar "f") (EData ["Int","2"] EUnit)))))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","3"] EUnit)

    it "ret f(1,2)" $
      steps (
        (SVar ("+", Nothing)
        (SVar ("f", Just $ EFunc (SRet (ECall (EVar "+") (EVar "_arg"))))
        (SRet (ECall (EVar "f") (ETuple [EData ["Int","1"] EUnit,EData ["Int","2"] EUnit])))))
        , [("_steps",Just $ EData ["Int","0"] EUnit)])
      `shouldBe` (EData ["Int","3"] EUnit)

  --------------------------------------------------------------------------
  describe "go" $ do

    describe "write" $ do

      it "(a,b) <- (1,2)" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "a" ((TTop False),cz)
          (B.SVar annz "b" ((TTop False),cz)
          (mmmOne annz False (B.ETuple annz [B.EVar annz "a",B.EVar annz "b"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]])
            (B.SRet annz (B.EVar annz "b"))
            (B.SRet annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "(_,b) <- (1,2)" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "a" ((TTop False),cz)
          (B.SVar annz "b" ((TTop False),cz)
          (mmmOne annz False (B.ETuple annz [B.EAny annz,B.EVar annz "b"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]])
            (B.SRet annz (B.EVar annz "b"))
            (B.SRet annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "1 <- 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (mmmOne annz False (B.ECons annz ["Int","1"]) (B.ECons annz ["Int","1"])
            (B.SRet annz (B.ECons annz ["Int","2"]))
            (B.SRet annz (B.EError annz 99))))
          `shouldBe` (EData ["Int","2"] EUnit)

      it "a <- 1 ; `a` <- 1" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.EExp annz $ B.EVar annz "a") (B.ECons annz ["Int","1"])
              (B.SRet   annz (B.EVar annz "a"))
              (B.SRet   annz (B.EError annz 99)))
            (B.SRet   annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "a <- 2 ; 1 <- a" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","2"])
            (mmmAny annz (B.ECons annz ["Int","1"]) (B.EVar annz "a")
              (B.SRet   annz (B.EVar annz "a"))
              (B.SRet   annz (B.EError annz 10)))
            (B.SRet   annz (B.EError annz 99)))))
        `shouldBe` (EError 10)

      it "a <- 1 ; 1 <- a" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.ECons annz ["Int","1"]) (B.EVar annz "a")
              (B.SRet   annz (B.EVar annz "a"))
              (B.SRet   annz (B.EError annz 99)))
            (B.SRet   annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "a <- 1 ; `a` <- 2" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "a" (int,cz)
          (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
            (mmmAny annz (B.EExp annz $ B.EVar annz "a") (B.ECons annz ["Int","2"])
              (B.SRet   annz (B.EVar annz "a"))
              (B.SRet   annz (B.EError annz 10)))
            (B.SRet   annz (B.EError annz 99)))))
        `shouldBe` (EError 10)

    describe "func" $ do

      it "Int ; f1 ; return f1 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "f1" (TFunc False (TUnit False) (int),cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (int),cz)
                          (B.SRet annz (B.ECons annz ["Int","1"])))
            (B.SRet annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
            (B.SRet annz (B.EError annz 99)))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "Int ; f1 (err!) ; return f1 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "f1" (TFunc False (TUnit False) (TUnit False),cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (TUnit False),cz)
                          (B.SRet annz (B.EError annz 1)))
            (B.SRet annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
            (B.SRet annz (B.EError annz 99)))))
        `shouldBe` (EError 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "f1" (TFunc False (TUnit False) (TUnit False),cz)
          (mmmOne annz False (B.EVar annz "f1")
                        (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (TUnit False),cz)
                          (B.SRet annz (B.EError annz 1)))
            (B.SSeq annz
              (B.SCall annz (B.ECall annz (B.EVar annz "f1") (B.EUnit annz)))
              (B.SRet annz (B.ECons annz ["Int","99"])))
            (B.SRet annz (B.EError annz 99)))))
        `shouldBe` (EError 1)

      it "Int ; f1 (err!) ; f1 ; ret 99" $
        go
          (B.SSeq annz
            (B.SCall annz (B.ECall annz (B.EError annz 1) (B.EUnit annz)))
            (B.SRet annz (B.EError annz 99)))
        `shouldBe` (EError 1)

      it "(f,g) <- (+,c) ; return f(g 1, g 2)" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
          (B.SVar annz "c" (TFunc False (int) (int),cz)
          (mmmOne annz False (B.EVar annz "c")
                        (B.EFunc annz B.FuncGlobal (TFunc False (int) (int),cz)
                          (B.SRet annz (B.EArg annz)))
            (B.SVar annz "f" (TFunc False (TTuple False [int, int]) (int),cz)
              (B.SVar annz "g" (TFunc False (int) (int),cz)
              (mmmOne annz False (B.ETuple annz [B.EVar annz "f",B.EVar annz "g"]) (B.ETuple annz [B.EVar annz "+",B.EVar annz "c"])
                (B.SRet annz
                  (B.ECall annz
                    (B.EVar annz "f")
                    (B.ETuple annz [
                      B.ECall annz (B.EVar annz "c") (B.ECons annz ["Int","1"]),
                      B.ECall annz (B.EVar annz "c") (B.ECons annz ["Int","2"])])))
                (B.SRet annz (B.EError annz 99)))))
            (B.SRet annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","3"] EUnit)

      it "glb <- 1 ; f () -> glb ; ret glb" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "glb" (int,cz)
          (mmmOne annz False (B.EVar annz "glb") (B.ECons annz ["Int","1"])
            (B.SVar   annz "f" (TFunc False (TUnit False) (int),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (int),cz)
                              (B.SRet annz (B.EVar annz "glb")))
                (B.SRet annz
                  (B.ECall annz (B.EVar annz "f") (B.EUnit annz)))
                (B.SRet annz (B.EError annz 99))))
            (B.SRet annz (B.EError annz 99)))))
          `shouldBe` (EData ["Int","1"] EUnit)

      it "glb <- 1 ; f() -> g() -> glb ; ret f()()" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "glb" (int,cz)
          (mmmOne annz False (B.EVar annz "glb") (B.ECons annz ["Int","1"])
            (B.SVar   annz "f" (TFunc False (TUnit False) (TFunc False (TUnit False) (int)),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (TFunc False (TUnit False) (int)),cz)
                              (B.SRet annz
                                (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (int),cz)
                                  (B.SRet annz (B.EVar annz "glb")))))
                (B.SRet annz
                  (B.ECall annz
                    (B.ECall annz (B.EVar annz "f") (B.EUnit annz))
                    (B.EUnit annz)))
                (B.SRet annz (B.EError annz 99))))
            (B.SRet annz (B.EError annz 99)))))
          `shouldBe` (EData ["Int","1"] EUnit)

      it "(TODO: loc lifetime) g' <- nil ; { loc <- 1 ; f() -> g() -> glb ; g' <- f() } ; ret g'()" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SVar   annz "g'" (TFunc False (TUnit False) (int),cz)
          (B.SVar   annz "loc" (int,cz)
          (mmmOne annz False (B.EVar annz "loc") (B.ECons annz ["Int","1"])
            (B.SVar   annz "f" (TFunc False (TUnit False) (TFunc False (TUnit False) (int)),cz)
              (mmmOne annz False (B.EVar annz "f")
                            (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (TFunc False (TUnit False) (int)),cz)
                              (B.SRet annz
                                (B.EFunc annz B.FuncGlobal (TFunc False (TUnit False) (int),cz)
                                  (B.SRet annz (B.EVar annz "loc")))))
                (mmmOne annz False (B.EVar annz "g'")
                              (B.ECall annz (B.EVar annz "f") (B.EUnit annz))
                  (B.SRet annz
                    (B.ECall annz (B.EVar annz "g'") (B.EUnit annz)))
                  (B.SRet annz (B.EError annz 99)))
                (B.SRet annz (B.EError annz 99))))
            (B.SRet annz (B.EError annz 99))))))
          `shouldBe` (EData ["Int","1"] EUnit)

    describe "data" $ do

      it "data X with Int ; x <- X 1 ; return x" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SData annz Nothing (TData False ["X"] [] int,cz) False
          (B.SVar annz "x" (TData False ["X"] [] (int),cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ECons annz ["Int","1"]))
            (B.SRet annz (B.EVar annz "x"))
            (B.SRet annz (B.EError annz 99))))))
        `shouldBe` (EData ["X"] (EData ["Int","1"] EUnit))

      it "data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
          (B.SData annz Nothing (TData False ["X"] [] (TTuple False [int, int]),cz) False
          (B.SVar annz "x" (TData False ["X"] [] (TTuple False [int, int]),cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ETuple annz [B.ECall annz (B.EVar annz "+") (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]]), B.ECons annz ["Int","3"]]))
            (B.SRet annz (B.EVar annz "x"))
            (B.SRet annz (B.EError annz 99)))))))
        `shouldBe` (EData ["X"] (ETuple [EData ["Int","3"] EUnit,EData ["Int","3"] EUnit]))

      it "TODO (coerse): data X with (Int,Int) ; x <- X (1,2) ; return +x" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
          (B.SData annz Nothing (TData False ["X"] [] (TTuple False [int, int]),cz) False
          (B.SVar annz "x" (TData False ["X"] [] (TUnit False),cz)
          (mmmOne annz False (B.EVar annz "x") (B.ECall annz (B.ECons annz ["X"]) (B.ETuple annz [B.ECons annz ["Int","1"],B.ECons annz ["Int","2"]]))
            (B.SRet annz (B.ECall annz (B.EVar annz "+") (B.EVar annz "x")))
            (B.SRet annz (B.EError annz 99)))))))
        `shouldBe` (EData ["X"] (EData ["Int","1"] EUnit))

      it "data X with Int ; x:Int ; X x <- X 1" $
        go
          (B.SData  annz Nothing (int,cz) False
          (B.SData  annz Nothing (TData False ["X"] [] int,cz) False
          (B.SVar   annz "x" (int,cz)
          (mmmOne annz False (B.ECall annz (B.ECons annz ["X"]) (B.EVar annz "x")) (B.ECall annz (B.ECons annz ["X"]) (B.ECons annz ["Int","1"]))
            (B.SRet   annz (B.EVar annz "x"))
            (B.SRet   annz (B.EError annz 99))))))
        `shouldBe` (EData ["Int","1"] EUnit)

    describe "class" $ do

      it "Int ; X a ; inst X Int ; return f3 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SClass annz "X" (cv "a")
            [(annz,"f3",(TFunc False (TAny False "a") (int),cvc ("a","X")),False)]
          (B.SVar annz "f3" (TFunc False (TAny False "a") (int),cvc ("a","X"))
          (B.SInst annz "X" (int,cz)
            [(annz,"f3",(TFunc False (int) (int),cz),True)]
            (B.SVar annz "$f3$(Int -> Int)$" (TFunc False (int) (int),cz)
            (mmmOne annz False
              (B.EVar annz "$f3$(Int -> Int)$")
              (B.EFunc annz B.FuncGlobal (TFunc False (int) (int),cz)
                (B.SRet annz (B.ECons annz ["Int","1"])))
              (B.SSeq annz
                (B.SNop annz)
                (B.SRet annz (B.ECall annz (B.EVar annz "f3") (B.ECons annz ["Int","1"]))))
              (B.SNop annz)))))))
        `shouldBe` (EData ["Int","1"] EUnit)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f2 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
          (B.SData annz Nothing (bool,cz) False
          (B.SClass annz "X" (cv "a")
            [(annz,"f2",(TFunc False (TAny False "a") (int),cvc ("a","X")),False)]
          (B.SVar annz "f2" (TFunc False (TAny False "a") (int),cvc ("a","X"))
          (B.SInst annz "X" (bool,cz)
            [(annz,"f2",(TFunc False (bool) (int),cz),True)]
            (B.SVar annz "$f2$(Bool -> Int)$" (TFunc False (bool) (int),cz)
            (mmmOne annz False
              (B.EVar annz "$f2$(Bool -> Int)$")
              (B.EFunc annz B.FuncGlobal (TFunc False (bool) (int),cz)
                (B.SRet annz (B.ECons annz ["Int","0"])))
              (B.SSeq annz
                (B.SNop annz)
                (B.SInst annz "X" (int,cz)
                  [(annz,"f2",(TFunc False (int) (int),cz),True)]
                  (B.SVar annz "$f2$(Int -> Int)$" (TFunc False (int) (int),cz)
                  (mmmOne annz False
                    (B.EVar annz "$f2$(Int -> Int)$")
                    (B.EFunc annz B.FuncGlobal (TFunc False (int) (int),cz)
                      (B.SRet annz
                        (B.ECall annz
                          (B.EVar annz "+")
                          (B.ETuple annz [B.EArg annz, B.ECons annz ["Int","1"]]))))
                    (B.SSeq annz
                      (B.SNop annz)
                      (B.SVar annz "ret" (int,cz)
                      (mmmOne annz False (B.EVar annz "ret")
                        (B.ECall annz (B.EVar annz "f2") (B.ECons annz ["Int","1"]))
                        (B.SRet annz (B.EVar annz "ret"))
                        (B.SRet annz (B.EError annz 99))))
                    )
                    (B.SNop annz))))
                    )
                    (B.SNop annz)))))))))
        `shouldBe` (EData ["Int","2"] EUnit)

      it "Int ; Bool ; X a ; inst X Bool/Int ; return f4 1" $
        go
          (B.SData annz Nothing (int,cz) False
          (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
          (B.SData annz Nothing (bool,cz) False
          (B.SClass annz "X" (cv "a")
            [(annz,"f4",(TFunc False (TAny False "a") (int),cvc ("a","X")),False)]
          (B.SVar annz "f4" (TFunc False (TAny False "a") (int),cvc ("a","X"))
          (B.SInst annz "X" (int,cz)
            [(annz,"f4",(TFunc False (int) (int),cz),True)]
            (B.SVar annz "$f4$(Int -> Int)$" (TFunc False (int) (int),cz)
            (mmmOne annz False
              (B.EVar annz "$f4$(Int -> Int)$")
              (B.EFunc annz B.FuncGlobal (TFunc False (int) (int),cz)
                (B.SRet annz
                  (B.ECall annz
                    (B.EVar annz "+")
                    (B.ETuple annz [B.EArg annz, B.ECons annz ["Int","1"]]))))
                (B.SSeq annz
                  (B.SNop annz)
                  (B.SInst annz "X" (bool,cz)
                    [(annz,"f4",(TFunc False (bool) (int),cz),True)]
                    (B.SVar annz "$f4$(Bool -> Int)$" (TFunc False (bool) (int),cz)
                    (mmmOne annz False
                      (B.EVar annz "$f4$(Bool -> Int)$")
                      (B.EFunc annz B.FuncGlobal (TFunc False (bool) (int),cz)
                        (B.SRet annz (B.ECons annz ["Int","0"])))
                      (B.SSeq annz
                        (B.SNop annz)
                        (B.SRet annz (B.ECall annz (B.EVar annz "f4") (B.ECons annz ["Int","1"])))
                      )
                      (B.SNop annz))))
                )
                (B.SNop annz)))))))))
        `shouldBe` (EData ["Int","2"] EUnit)

    describe "misc" $ do

      evalProgItSuccess (EData ["Int","11"] EUnit)
        (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
        (B.SVar annz "a" (int,cz)
        (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
          (B.SRet annz (B.ECall annz (B.EVar annz "+") (B.ETuple annz [(B.EVar annz "a"),(B.ECons annz ["Int","10"])])))
          (B.SRet annz (B.EError annz 99)))))

      evalProgItSuccess (EData ["Int","11"] EUnit)
        (B.SVar annz "+" (TFunc False (TTuple False [int, int]) (int),cz)
        (B.SVar annz "a" (int,cz)
        (mmmOne annz False (B.EVar annz "a") (B.ECons annz ["Int","1"])
          (B.SVar annz "b" (int,cz)
            (mmmOne annz False (B.EVar annz "b") (B.ECons annz ["Int","91"])
              (B.SRet annz
                (B.ECall annz (B.EVar annz "+")
                             (B.ETuple annz [(B.EVar annz "a"),(B.ECons annz ["Int","10"])])))
              (B.SRet annz (B.EError annz 92))))
          (B.SRet annz (B.EError annz 93)))))

      evalProgItSuccess (EData ["Int","1"] EUnit)
        (B.SRet annz (B.ECons annz ["Int","1"]) `B.sSeq`
            B.SVar annz "_" (int,cz) (B.SRet annz (B.ECons annz ["Int","2"])) `B.sSeq`
            B.SNop annz)

      where
        evalProgItSuccess res p =
          (it (printf "pass: %s ~> %s" "todo" (show res)) $
            (go (B.prelude annz p) `shouldBe` res))
