module Ceu.FullSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace
import Data.Map as M (fromList)

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..))
import Ceu.Grammar.Ann          (Ann(type_),annz)

import qualified Ceu.Grammar.Basic as B
import qualified Ceu.Eval as E

import Ceu.Grammar.Full.Full
import Ceu.Grammar.Full.Eval
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Func  as Func

main :: IO ()
main = hspec spec

setb z chk loc exp p1 p2 = B.SMatch  z chk   exp [(B.SNop z,loc,p1)]
set  z     loc exp p1 p2 =   SMatch  z False exp [(  SNop z,loc,p1)]
set' z chk loc exp p1 p2 =   SMatch' z chk   exp [(  SNop z,loc,p1)]

spec :: Spec
spec = do

{-
  describe "TODO" $ do
    it "TODO" $
      compile' (SSeq annz (SData annz Nothing ["Int"] [] (TUnit False) False) (SSeq annz (SSeq annz (SVar annz "x" (TData False ["Int"])) (SNop annz)) (SSeq annz (SSet annz False (EVar annz "x") (ECons annz ["Int","1"])) (SRet annz (ECons annz ["Int","1"])))))
      `shouldBe` ([], (B.SVar annz "x" (TUnit False) (B.SNop annz)))
-}

  --------------------------------------------------------------------------
            --"   func f1 x : (a -> Bool) do return f2 x end",

  describe "EFunc.compile" $ do

    it "func id : (a->a) do end" $ do
      Func.compile (SFunc annz "id" (TFunc False (TAny False "a") (TAny False "a"),cz) (SNop annz))
      `shouldBe` (SSeq annz
                  (SVar annz "id" (TFunc False (TAny False "a") (TAny False "a"),cz))
                  (SSet annz False (EVar annz "id")
                    (EFunc annz (TFunc False (TAny False "a") (TAny False "a"),cz) (SNop annz))))

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (SVar annz "x" ((TUnit False),cz))
        `shouldBe` (SVar'' annz "x" ((TUnit False),cz) (SNop annz))

      it "var x; (SNop annz)" $ do
        Scope.compile (SSeq annz (SVar annz "x" ((TUnit False),cz)) (SNop annz))
        `shouldBe` (SVar'' annz "x" ((TUnit False),cz) (SNop annz))

      it "var x <- 1 ; (SNop annz)" $ do
        Scope.compile (SSeq annz (SVar annz "x" (int,cz)) (SSeq annz (SSet annz False (EVar annz "x") (ECons annz ["Int","1"])) (SNop annz)))
        `shouldBe` (SVar'' annz "x" (int,cz) (SSeq annz (SSet annz False (EVar annz "x") (ECons annz ["Int","1"])) (SNop annz)))

      it "scope var x end ; var y" $ do
        Scope.compile (SSeq annz (SScope annz (SVar annz "x" ((TUnit False),cz))) (SVar annz "y" ((TUnit False),cz)))
        `shouldBe` SSeq annz (SVar'' annz "x" ((TUnit False),cz) (SNop annz)) (SVar'' annz "y" ((TUnit False),cz) (SNop annz))

      it "scope var x end ; x=1" $ do
        compile' (SSeq annz (SScope annz (SVar annz "x" (int,cz))) (SSet annz False (EVar annz "x") (ECons annz ["Int","1"])))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared","data 'Int.1' is not declared"], B.SSeq annz (B.SVar annz "x" (int,cz) (B.SNop annz)) (setb annz False (B.EVar annz "x") (B.ECons (annz{type_=(TAny False "?",cz)}) ["Int","1"]) (B.SNop annz) (B.SRet annz (B.EError annz (-2)))))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (SVar'' annz "x" ((TUnit False),cz) (SNop annz))
      `shouldBe` ([], (B.SVar annz "x" ((TUnit False),cz) (B.SNop annz)))

    it "do var x; x = 1 end" $ do
      compile' (SVar'' annz "x" (int,cz) (set' annz False (EVar annz "x") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.SVar annz "x" (int,cz) (setb annz False (B.EVar annz "x") (B.ECons annz{type_=(TData False ["Int"] [] (TUnit False),cz)} ["Int","1"]) (B.SNop annz) (B.SNop annz))))

    it "do var x; x = 1 end" $ do
      compile' (SVar'' annz "x" (int,cz) (set' annz False (EVar annz "x") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.SVar annz "x" (int,cz) (setb annz False (B.EVar annz "x") (B.ECons annz{type_=(TData False ["Int"] [] (TUnit False),cz)} ["Int","1"]) (B.SNop annz) (B.SNop annz))))

    it "if" $
      compile
        (SSeq annz
            (set annz
                (EExp annz (EVar annz "_true"))
                (ECall annz (ECons annz ["Bool","False"]) (EUnit annz))
                (SNop annz)
                (SNop annz))
            (SRet annz (ECons annz ["Int","10"])))
      `shouldBe` SSeq annz (set' annz False (EExp annz (EVar annz "_true")) (ECall annz (ECons annz ["Bool","False"]) (EUnit annz)) (SNop annz) (SNop annz)) (SRet annz (ECons annz ["Int","10"]))

    it "class/inst/0" $ do
      compile (SInst annz "F3able" (int,cz)
                (SFunc annz "f3" (TFunc False (TAny False "Int") (int),cz)
                  (SRet annz (ECons annz ["Int","10"]))))
      `shouldBe`
        (SInst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc False (TAny False "Int") (int),cz),True)]
        (SVar'' annz "$f3$(Int -> Int)$" (TFunc False (TAny False "Int") (int),cz)
          (set' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc False (TAny False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"]))) (SNop annz) (SRet annz (EError annz (-2))))))

    it "class/inst/1" $ do
      compile (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SVar annz "f3" (TFunc False (TAny False "a") (int),cz)))
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc False (TAny False "Int") (int),cz)
                    (SRet annz (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClass'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc False (TAny False "a") (int),cvc("a","F3able")),False)]
        (SVar'' annz "f3" (TFunc False (TAny False "a") (int),cvc("a","F3able"))
        (SInst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc False (TAny False "Int") (int),cz),True)]
        (SVar'' annz "$f3$(Int -> Int)$" (TFunc False (TAny False "Int") (int),cz)
            (set' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc False (TAny False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"]))) (SNop annz) (SRet annz (EError annz (-2))))))))

    it "class/inst/2" $ do
      compile (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SVar annz "f3" (TFunc False (TAny False "a") (int),cz)))
              (SSeq annz
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc False (TAny False "Int") (int),cz)
                    (SRet annz (ECons annz ["Int","10"]))))
              (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClass'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc False (TAny False "a") (int),cvc("a","F3able")),False)]
        (SVar'' annz "f3" (TFunc False (TAny False "a") (int),cvc("a","F3able"))
        (SInst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc False (TAny False "Int") (int),cz),True)]
        (SVar'' annz "$f3$(Int -> Int)$" (TFunc False (TAny False "Int") (int),cz)
          (SSeq annz
            (set' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc False (TAny False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"])))
              (SNop annz)
              (SRet annz (EError annz (-2))))
            (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))))))
    it "class/inst/3" $ do
      compile (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SSeq annz
                  (SSeq annz
                  (SVar annz "f3" (TFunc False (TAny False "a") (int),cz))
                  (SNop annz))
                  (SNop annz)))
                (SSeq annz
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc False (TAny False "Int") (int),cz)
                    (SSeq annz
                    (SSeq annz
                    (SVar annz "v" (TAny False "Int",cz))
                    (SNop annz))
                    (SSeq annz
                    (SSet annz False (EVar annz "v") (EArg annz))
                    (SRet annz (EVar annz "v"))))))
                (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClass'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc False (TAny False "a") (int),cvc("a","F3able")),False)]
        (SVar'' annz "f3" (TFunc False (TAny False "a") (int),cvc("a","F3able"))
        (SSeq annz
        (SNop annz)
        (SSeq annz
        (SNop annz)
        (SInst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc False (TAny False "Int") (int),cz),True)]
          (SVar'' annz "$f3$(Int -> Int)$" (TFunc False (TAny False "Int") (int),cz)
          (SSeq annz
            (set' annz False (EVar annz "$f3$(Int -> Int)$")
              (EFunc annz (TFunc False (TAny False "Int") (int),cz)
                (SVar'' annz "v" (TAny False "Int",cz)
                (SSeq annz
                (SNop annz)
                (SSeq annz
                  (set' annz False (EVar annz "v") (EArg annz)
                    (SNop annz)
                    (SRet annz (EError annz (-2))))
                  (SRet annz (EVar annz "v"))))))
              (SNop annz)
              (SRet annz (EError annz (-2))))
            (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))))))))

    it "Xxx.Yyy" $
      compile (SSeq annz (SData annz Nothing (int,                         M.fromList []) False)
              (SSeq annz (SData annz Nothing (TData False ["Xxx"]       [] int,  M.fromList []) True)
              (SSeq annz (SData annz Nothing (TData False ["Xxx","Yyy"] [] int,  M.fromList []) False)
              (SSeq annz
              (SSeq annz (SVar annz "y" (TData False ["Xxx","Yyy"] [] (TUnit False),M.fromList []))
                        (SNop annz))
                        (SSet annz False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])))))))
      `shouldBe`
        --(SData'' annz Nothing (TData False ["Int"] [] (TUnit False),fromList []) False (SData'' annz Nothing (TData False ["Xxx"] [] int,fromList []) True (SData'' annz Nothing (TData False ["Xxx","Yyy"] [] (TTuple False [int,int]),fromList []) False (SVar'' annz "y" (TData False ["Xxx","Yyy"] [] (TTuple False [int,int]),fromList []) (SSeq annz (SNop annz) (set' annz False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])) (SNop annz) (SRet annz (EError annz (-2)))))))))
        SData'' annz Nothing (TData False ["Int"] [] (TUnit False),fromList []) False (SData'' annz Nothing (TData False ["Xxx"] [] (TData False ["Int"] [] (TUnit False)),fromList []) True (SVar'' annz "Xxx._1" (TFunc False (TData False ["Xxx"] [] (TData False ["Int"] [] (TUnit False))) (TData False ["Int"] [] (TUnit False)),fromList []) (SMatch' annz False (EFunc annz (TFunc False (TData False ["Xxx"] [] (TData False ["Int"] [] (TUnit False))) (TData False ["Int"] [] (TUnit False)),fromList []) (SVar'' annz "ret" (TData False ["Int"] [] (TUnit False),fromList []) (SMatch' annz False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx"]) (EVar annz "ret"),SRet annz (EVar annz "ret"))]))) [(SNop annz,EVar annz "Xxx._1",SData'' annz Nothing (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]),fromList []) False (SVar'' annz "Xxx.Yyy._2" (TFunc False (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)])) (TData False ["Int"] [] (TUnit False)),fromList []) (SMatch' annz False (EFunc annz (TFunc False (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)])) (TData False ["Int"] [] (TUnit False)),fromList []) (SVar'' annz "ret" (TData False ["Int"] [] (TUnit False),fromList []) (SMatch' annz False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [EAny annz,EVar annz "ret"]),SRet annz (EVar annz "ret"))]))) [(SNop annz,EVar annz "Xxx.Yyy._2",SVar'' annz "Xxx.Yyy._1" (TFunc False (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)])) (TData False ["Int"] [] (TUnit False)),fromList []) (SMatch' annz False (EFunc annz (TFunc False (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)])) (TData False ["Int"] [] (TUnit False)),fromList []) (SVar'' annz "ret" (TData False ["Int"] [] (TUnit False),fromList []) (SMatch' annz False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [EVar annz "ret",EAny annz]),SRet annz (EVar annz "ret"))]))) [(SNop annz,EVar annz "Xxx.Yyy._1",SVar'' annz "y" (TData False ["Xxx","Yyy"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]),fromList []) (SSeq annz (SNop annz) (SMatch' annz False (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])) [(SNop annz,EVar annz "y",SNop annz)])))]))])))])))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (prelude annz $ SRet annz (ECons annz ["Int","1"]))
      `shouldBe` Right (E.EData ["Int","1"] E.EUnit)

    it "data X with Int ; x:Int ; X 1 <- X 2" $ do
      go (prelude annz $ SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,cz) False) (SSeq annz (SSet annz False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"]))) (SRet annz (ECons annz ["Int","2"]))))
      `shouldBe`
        Left ["match never succeeds : data mismatch"] --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (prelude annz $ SSeq annz
          (SCall annz (ECall annz
                        (EFunc annz (TFunc False (TUnit False) (TUnit False),cz)
                          (SRet annz (EUnit annz))) (EUnit annz)))
          (SRet annz (ECons annz ["Int","10"])))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (prelude annz $ SRet annz
            (ECall annz
              (EFunc annz (TFunc False (TUnit False) (int),cz)
                (SRet annz (ECons annz ["Int","10"])))
              (EUnit annz)))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)
