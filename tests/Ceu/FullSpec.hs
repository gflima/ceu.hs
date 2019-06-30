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
      compile' (Seq annz (Data annz ["Int"] [] Type0 False) (Seq annz (Seq annz (Var annz "x" (TypeD ["Int"])) (Nop annz)) (Seq annz (Set annz False (LVar "x") (Cons annz ["Int","1"])) (Ret annz (Cons annz ["Int","1"])))))
      `shouldBe` ([], (B.Var annz "x" Type0 (B.Nop annz)))
-}

  --------------------------------------------------------------------------
            --"   func f1 x : (a -> Bool) do return f2 x end",

  describe "Func.compile" $ do

    it "func id : (a->a) do end" $ do
      FuncS.compile (FuncS annz "id" (TypeF (TypeV "a") (TypeV "a"),cz) (Nop annz))
      `shouldBe` (Seq annz
                  (Var annz "id" (TypeF (TypeV "a") (TypeV "a"),cz))
                  (Set annz False (LVar "id")
                    (Func annz (TypeF (TypeV "a") (TypeV "a"),cz) (Nop annz))))

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var annz "x" (Type0,cz))
        `shouldBe` (Var'' annz "x" (Type0,cz) (Nop annz))

      it "var x; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (Type0,cz)) (Nop annz))
        `shouldBe` (Var'' annz "x" (Type0,cz) (Nop annz))

      it "var x <- 1 ; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (int,cz)) (Seq annz (Set annz False (LVar "x") (Cons annz ["Int","1"])) (Nop annz)))
        `shouldBe` (Var'' annz "x" (int,cz) (Seq annz (Set annz False (LVar "x") (Cons annz ["Int","1"])) (Nop annz)))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var annz "x" (Type0,cz))) (Var annz "y" (Type0,cz)))
        `shouldBe` Seq annz (Var'' annz "x" (Type0,cz) (Nop annz)) (Var'' annz "y" (Type0,cz) (Nop annz))

      it "scope var x end ; x=1" $ do
        compile' (Seq annz (Scope annz (Var annz "x" (int,cz))) (Set annz False (LVar "x") (Cons annz ["Int","1"])))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared","data 'Int.1' is not declared"], B.Seq annz (B.Var annz "x" (int,cz) (B.Nop annz)) (B.Match annz False (B.LVar "x") (B.Cons (annz{type_=(TypeV "?",cz)}) ["Int","1"]) (B.Nop annz) (B.Ret annz (B.Error annz (-2)))))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (Var'' annz "x" (Type0,cz) (Nop annz))
      `shouldBe` ([], (B.Var annz "x" (Type0,cz) (B.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (int,cz) (Match' annz False (LVar "x") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.Var annz "x" (int,cz) (B.Match annz False (B.LVar "x") (B.Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (B.Nop annz) (B.Nop annz))))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (int,cz) (Match' annz False (LVar "x") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.Var annz "x" (int,cz) (B.Match annz False (B.LVar "x") (B.Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (B.Nop annz) (B.Nop annz))))

    it "if" $
      compile
        (Seq annz
            (Match annz
                (LExp (Read annz "_true"))
                (Call annz (Cons annz ["Bool","False"]) (Unit annz))
                (Nop annz)
                (Nop annz))
            (Ret annz (Cons annz ["Int","10"])))
      `shouldBe` Seq annz (Match' annz True (LExp (Read annz "_true")) (Call annz (Cons annz ["Bool","False"]) (Unit annz)) (Nop annz) (Nop annz)) (Ret annz (Cons annz ["Int","10"]))

    it "class/inst/0" $ do
      compile (Inst annz "F3able" (int,cz)
                (FuncS annz "f3" (TypeF (TypeV "Int") (int),cz)
                  (Ret annz (Cons annz ["Int","10"]))))
      `shouldBe`
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TypeF (TypeV "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (int),cz)
          (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (int),cz) (Ret annz (Cons annz ["Int","10"]))) (Nop annz) (Ret annz (Error annz (-2))))))

    it "class/inst/1" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TypeF (TypeV "a") (int),cz)))
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (int),cz)
                    (Ret annz (Cons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (int),cvc("a","F3able"))
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TypeF (TypeV "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (int),cz)
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (int),cz) (Ret annz (Cons annz ["Int","10"]))) (Nop annz) (Ret annz (Error annz (-2))))))))

    it "class/inst/2" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TypeF (TypeV "a") (int),cz)))
              (Seq annz
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (int),cz)
                    (Ret annz (Cons annz ["Int","10"]))))
              (Ret annz (Call annz (Read annz "f3") (Cons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (int),cvc("a","F3able"))
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TypeF (TypeV "Int") (int),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (int),cz)
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (int),cz) (Ret annz (Cons annz ["Int","10"])))
              (Seq annz
                (Nop annz)
                (Ret annz (Call annz (Read annz "f3") (Cons annz ["Int","10"]))))
              (Ret annz (Error annz (-2))))))))
    it "class/inst/3" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Seq annz
                  (Seq annz
                  (Var annz "f3" (TypeF (TypeV "a") (int),cz))
                  (Nop annz))
                  (Nop annz)))
                (Seq annz
                (Inst annz "F3able" (int,cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (int),cz)
                    (Seq annz
                    (Seq annz
                    (Var annz "v" (TypeV "Int",cz))
                    (Nop annz))
                    (Seq annz
                    (Set annz False (LVar "v") (Arg annz))
                    (Ret annz (Read annz "v"))))))
                (Ret annz (Call annz (Read annz "f3") (Cons annz ["Int","10"])))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (int),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (int),cvc("a","F3able"))
        (Seq annz
        (Nop annz)
        (Seq annz
        (Nop annz)
        (Inst'' annz "F3able" (int,cz)
          [(annz,"f3",(TypeF (TypeV "Int") (int),cz),True)]
          (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (int),cz)
          (Match' annz False
            (LVar "$f3$(Int -> Int)$")
            (Func annz (TypeF (TypeV "Int") (int),cz)
              (Var'' annz "v" (TypeV "Int",cz)
              (Seq annz
              (Nop annz)
              (Match' annz False (LVar "v") (Arg annz) (Seq annz (Nop annz) (Ret annz (Read annz "v"))) (Ret annz (Error annz (-2)))))))
            (Seq annz
              (Nop annz)
              (Ret annz (Call annz (Read annz "f3") (Cons annz ["Int","10"]))))
            (Ret annz (Error annz (-2))))))))))

    it "Xxx.Yyy" $
      compile (Seq annz (Data annz (int,                            M.fromList []) False)
              (Seq annz (Data annz (TypeD ["Xxx"]       [] int,  M.fromList []) False)
              (Seq annz (Data annz (TypeD ["Xxx","Yyy"] [] int,  M.fromList []) False)
              (Seq annz
              (Seq annz (Var annz "y" (TypeD ["Xxx","Yyy"] [] Type0,M.fromList []))
                        (Nop annz))
                        (Set annz False (LVar "y") (Call annz (Cons annz ["Xxx","Yyy"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"]])))))))
      `shouldBe`
        (Data'' annz (TypeD ["Int"] [] Type0,fromList []) False (Data'' annz (TypeD ["Xxx"] [] int,fromList []) False (Data'' annz (TypeD ["Xxx","Yyy"] [] (TypeN [int,int]),fromList []) False (Var'' annz "y" (TypeD ["Xxx","Yyy"] [] (TypeN [int,int]),fromList []) (Seq annz (Nop annz) (Match' annz False (LVar "y") (Call annz (Cons annz ["Xxx","Yyy"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"]])) (Nop annz) (Ret annz (Error annz (-2)))))))))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (prelude annz $ Ret annz (Cons annz ["Int","1"]))
      `shouldBe` Right (E.Cons' ["Int","1"] E.Unit)

    it "data X with Int ; x:Int ; X 1 <- X 2" $ do
      go (prelude annz $ Seq annz (Data annz (TypeD ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (LCons ["Xxx"] (LCons ["Int","1"] LUnit)) (Call annz (Cons annz ["Xxx"]) (Cons annz ["Int","2"]))) (Ret annz (Cons annz ["Int","2"]))))
      `shouldBe`
        Left ["match never succeeds : data mismatch"] --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (prelude annz $ Seq annz
          (CallS annz (Call annz
                        (Func annz (TypeF Type0 Type0,cz)
                          (Ret annz (Unit annz))) (Unit annz)))
          (Ret annz (Cons annz ["Int","10"])))
      `shouldBe` Right (E.Cons' ["Int","10"] E.Unit)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (prelude annz $ Ret annz
            (Call annz
              (Func annz (TypeF Type0 (int),cz)
                (Ret annz (Cons annz ["Int","10"])))
              (Unit annz)))
      `shouldBe` Right (E.Cons' ["Int","10"] E.Unit)
