module Ceu.FullSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace
import Data.Map as M (fromList)

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..))
import Ceu.Grammar.Ann      (Ann(type_),annz)

import qualified Ceu.Grammar.Basic as B
import qualified Ceu.Eval as E

import Ceu.Grammar.Full.Full
import Ceu.Grammar.Full.Eval
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.FuncS as FuncS

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

{-
  describe "TODO" $ do
    it "TODO" $
      compile' (Seq annz (Data annz ["Int"] [] TUnit False) (Seq annz (Seq annz (Var annz "x" (TData ["Int"])) (Nop annz)) (Seq annz (Set annz False (EVar annz "x") (ECons annz ["Int","1"])) (Ret annz (ECons annz ["Int","1"])))))
      `shouldBe` ([], (B.Var annz "x" TUnit (B.Nop annz)))
-}

  --------------------------------------------------------------------------
            --"   func f1 x : (a -> Bool) do return f2 x end",

  describe "EFunc.compile" $ do

    it "func id : (a->a) do end" $ do
      FuncS.compile (FuncS annz "id" (TFunc (TAny "a") (TAny "a"),cz) (Nop annz))
      `shouldBe` (Seq annz
                  (Var annz "id" (TFunc (TAny "a") (TAny "a"),cz))
                  (Set annz False (EVar annz "id")
                    (EFunc annz (TFunc (TAny "a") (TAny "a"),cz) (Nop annz))))

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var annz "x" (TUnit,cz))
        `shouldBe` (Var'' annz "x" (TUnit,cz) (Nop annz))

      it "var x; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (TUnit,cz)) (Nop annz))
        `shouldBe` (Var'' annz "x" (TUnit,cz) (Nop annz))

      it "var x <- 1 ; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (int,cz)) (Seq annz (Set annz False (EVar annz "x") (ECons annz ["Int","1"])) (Nop annz)))
        `shouldBe` (Var'' annz "x" (int,cz) (Seq annz (Set annz False (EVar annz "x") (ECons annz ["Int","1"])) (Nop annz)))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var annz "x" (TUnit,cz))) (Var annz "y" (TUnit,cz)))
        `shouldBe` Seq annz (Var'' annz "x" (TUnit,cz) (Nop annz)) (Var'' annz "y" (TUnit,cz) (Nop annz))

      it "scope var x end ; x=1" $ do
        compile' (Seq annz (Scope annz (Var annz "x" (int,cz))) (Set annz False (EVar annz "x") (ECons annz ["Int","1"])))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared","data 'Int.1' is not declared"], B.Seq annz (B.Var annz "x" (int,cz) (B.Nop annz)) (B.Match annz False (B.EVar annz "x") (B.ECons (annz{type_=(TAny "?",cz)}) ["Int","1"]) (B.Nop annz) (B.Ret annz (B.EError annz (-2)))))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (Var'' annz "x" (TUnit,cz) (Nop annz))
      `shouldBe` ([], (B.Var annz "x" (TUnit,cz) (B.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (int,cz) (Match' annz False (EVar annz "x") (ECons annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.Var annz "x" (int,cz) (B.Match annz False (B.EVar annz "x") (B.ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (B.Nop annz) (B.Nop annz))))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (int,cz) (Match' annz False (EVar annz "x") (ECons annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.Var annz "x" (int,cz) (B.Match annz False (B.EVar annz "x") (B.ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (B.Nop annz) (B.Nop annz))))

    it "if" $
      compile
        (Seq annz
            (Match annz
                (EExp annz (EVar annz "_true"))
                (ECall annz (ECons annz ["Bool","False"]) (EUnit annz))
                (Nop annz)
                (Nop annz))
            (Ret annz (ECons annz ["Int","10"])))
      `shouldBe` Seq annz (Match' annz True (EExp annz (EVar annz "_true")) (ECall annz (ECons annz ["Bool","False"]) (EUnit annz)) (Nop annz) (Nop annz)) (Ret annz (ECons annz ["Int","10"]))

    it "class/inst/0" $ do
      compile (Inst annz "F3able" (int,cz)
                (FuncS annz "f3" (TFunc (TAny "Int") (int),cz)
                  (Ret annz (ECons annz ["Int","10"]))))
      `shouldBe`
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc (TAny "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TFunc (TAny "Int") (int),cz)
          (Match' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc (TAny "Int") (int),cz) (Ret annz (ECons annz ["Int","10"]))) (Nop annz) (Ret annz (EError annz (-2))))))

    it "class/inst/1" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TFunc (TAny "a") (int),cz)))
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TFunc (TAny "Int") (int),cz)
                    (Ret annz (ECons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc (TAny "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TFunc (TAny "a") (int),cvc("a","F3able"))
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc (TAny "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TFunc (TAny "Int") (int),cz)
            (Match' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc (TAny "Int") (int),cz) (Ret annz (ECons annz ["Int","10"]))) (Nop annz) (Ret annz (EError annz (-2))))))))

    it "class/inst/2" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TFunc (TAny "a") (int),cz)))
              (Seq annz
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TFunc (TAny "Int") (int),cz)
                    (Ret annz (ECons annz ["Int","10"]))))
              (Ret annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc (TAny "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TFunc (TAny "a") (int),cvc("a","F3able"))
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc (TAny "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TFunc (TAny "Int") (int),cz)
            (Match' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc annz (TFunc (TAny "Int") (int),cz) (Ret annz (ECons annz ["Int","10"])))
              (Seq annz
                (Nop annz)
                (Ret annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))
              (Ret annz (EError annz (-2))))))))
    it "class/inst/3" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Seq annz
                  (Seq annz
                  (Var annz "f3" (TFunc (TAny "a") (int),cz))
                  (Nop annz))
                  (Nop annz)))
                (Seq annz
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TFunc (TAny "Int") (int),cz)
                    (Seq annz
                    (Seq annz
                    (Var annz "v" (TAny "Int",cz))
                    (Nop annz))
                    (Seq annz
                    (Set annz False (EVar annz "v") (EArg annz))
                    (Ret annz (EVar annz "v"))))))
                (Ret annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TFunc (TAny "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TFunc (TAny "a") (int),cvc("a","F3able"))
        (Seq annz
        (Nop annz)
        (Seq annz
        (Nop annz)
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TFunc (TAny "Int") (int),cz),True)]
          (Var'' annz "$f3$(Int -> Int)$" (TFunc (TAny "Int") (int),cz)
          (Match' annz False
            (EVar annz "$f3$(Int -> Int)$")
            (EFunc annz (TFunc (TAny "Int") (int),cz)
              (Var'' annz "v" (TAny "Int",cz)
              (Seq annz
              (Nop annz)
              (Match' annz False (EVar annz "v") (EArg annz) (Seq annz (Nop annz) (Ret annz (EVar annz "v"))) (Ret annz (EError annz (-2)))))))
            (Seq annz
              (Nop annz)
              (Ret annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))
            (Ret annz (EError annz (-2))))))))))

    it "Xxx.Yyy" $
      compile (Seq annz (Data annz (int,                            M.fromList []) False)
              (Seq annz (Data annz (TData ["Xxx"]       [] int,  M.fromList []) False)
              (Seq annz (Data annz (TData ["Xxx","Yyy"] [] int,  M.fromList []) False)
              (Seq annz
              (Seq annz (Var annz "y" (TData ["Xxx","Yyy"] [] TUnit,M.fromList []))
                        (Nop annz))
                        (Set annz False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])))))))
      `shouldBe`
        (Data'' annz (TData ["Int"] [] TUnit,fromList []) False (Data'' annz (TData ["Xxx"] [] int,fromList []) False (Data'' annz (TData ["Xxx","Yyy"] [] (TTuple [int,int]),fromList []) False (Var'' annz "y" (TData ["Xxx","Yyy"] [] (TTuple [int,int]),fromList []) (Seq annz (Nop annz) (Match' annz False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])) (Nop annz) (Ret annz (EError annz (-2)))))))))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (prelude annz $ Ret annz (ECons annz ["Int","1"]))
      `shouldBe` Right (E.EData ["Int","1"] E.EUnit)

    it "data X with Int ; x:Int ; X 1 <- X 2" $ do
      go (prelude annz $ Seq annz (Data annz (TData ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"]))) (Ret annz (ECons annz ["Int","2"]))))
      `shouldBe`
        Left ["match never succeeds : data mismatch"] --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (prelude annz $ Seq annz
          (CallS annz (ECall annz
                        (EFunc annz (TFunc TUnit TUnit,cz)
                          (Ret annz (EUnit annz))) (EUnit annz)))
          (Ret annz (ECons annz ["Int","10"])))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (prelude annz $ Ret annz
            (ECall annz
              (EFunc annz (TFunc TUnit (int),cz)
                (Ret annz (ECons annz ["Int","10"])))
              (EUnit annz)))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)
