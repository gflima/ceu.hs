module Ceu.FullSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace

import Ceu.Grammar.Globals
import Ceu.Grammar.Type     (Type(..), cz,cv,cvc)
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
      compile' (Seq annz (Data annz ["Int"] [] Type0 False) (Seq annz (Seq annz (Var annz "x" (TypeD ["Int"])) (Nop annz)) (Seq annz (Set annz False (LVar "x") (Number annz 1)) (Ret annz (Number annz 1)))))
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
        Scope.compile (Seq annz (Var annz "x" (TypeD ["Int"],cz)) (Seq annz (Set annz False (LVar "x") (Number annz 1)) (Nop annz)))
        `shouldBe` (Var'' annz "x" (TypeD ["Int"],cz) (Seq annz (Set annz False (LVar "x") (Number annz 1)) (Nop annz)))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var annz "x" (Type0,cz))) (Var annz "y" (Type0,cz)))
        `shouldBe` Seq annz (Var'' annz "x" (Type0,cz) (Nop annz)) (Var'' annz "y" (Type0,cz) (Nop annz))

      it "scope var x end ; x=1" $ do
        compile' (Seq annz (Scope annz (Var annz "x" (TypeD ["Int"],cz))) (Set annz False (LVar "x") (Number annz 1)))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared"], B.Seq annz (B.Var annz "x" (TypeD ["Int"],cz) (B.Nop annz)) (B.Match annz False (B.LVar "x") (B.Number (annz{type_=(TypeD ["Int","1"],cz)}) 1) (B.Nop annz) (B.Ret annz (B.Error annz (-2)))))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (Var'' annz "x" (Type0,cz) (Nop annz))
      `shouldBe` ([], (B.Var annz "x" (Type0,cz) (B.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (TypeD ["Int"],cz) (Match' annz False (LVar "x") (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared"], (B.Var annz "x" (TypeD ["Int"],cz) (B.Match annz False (B.LVar "x") (B.Number annz{type_=(TypeD ["Int","1"],cz)} 1) (B.Nop annz) (B.Nop annz))))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" (TypeD ["Int"],cz) (Match' annz False (LVar "x") (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared"], (B.Var annz "x" (TypeD ["Int"],cz) (B.Match annz False (B.LVar "x") (B.Number annz{type_=(TypeD ["Int","1"],cz)} 1) (B.Nop annz) (B.Nop annz))))

    it "if" $
      compile
        (Seq annz
            (Match annz
                (LExp (Read annz "_true"))
                (Cons annz ["Bool","False"] (Unit annz))
                (Nop annz)
                (Nop annz))
            (Ret annz (Number annz 10)))
      `shouldBe` Seq annz (Match' annz True (LExp (Read annz "_true")) (Cons annz ["Bool","False"] (Unit annz)) (Nop annz) (Nop annz)) (Ret annz (Number annz 10))

    it "class/inst/0" $ do
      compile (Inst annz "F3able" (TypeD ["Int"],cz)
                (FuncS annz "f3" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
                  (Ret annz (Number annz 10))))
      `shouldBe`
        (Inst'' annz "F3able" (TypeD ["Int"],cz)
          [(annz,"f3",(TypeF (TypeV "Int") (TypeD ["Int"]),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
          (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (TypeD ["Int"]),cz) (Ret annz (Number annz 10))) (Nop annz) (Ret annz (Error annz (-2))))))

    it "class/inst/1" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cz)))
                (Inst annz "F3able" (TypeD ["Int"],cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
                    (Ret annz (Number annz 10)))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able"))
        (Inst'' annz "F3able" (TypeD ["Int"],cz)
          [(annz,"f3",(TypeF (TypeV "Int") (TypeD ["Int"]),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (TypeD ["Int"]),cz) (Ret annz (Number annz 10))) (Nop annz) (Ret annz (Error annz (-2))))))))

    it "class/inst/2" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Var annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cz)))
              (Seq annz
                (Inst annz "F3able" (TypeD ["Int"],cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
                    (Ret annz (Number annz 10))))
              (Ret annz (Call annz (Read annz "f3") (Number annz 10)))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able"))
        (Inst'' annz "F3able" (TypeD ["Int"],cz)
          [(annz,"f3",(TypeF (TypeV "Int") (TypeD ["Int"]),cz),True)]
        (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int") (TypeD ["Int"]),cz) (Ret annz (Number annz 10)))
              (Seq annz
                (Nop annz)
                (Ret annz (Call annz (Read annz "f3") (Number annz 10))))
              (Ret annz (Error annz (-2))))))))
    it "class/inst/3" $ do
      compile (Seq annz
                (Class annz "F3able" (cv "a")
                  (Seq annz
                  (Seq annz
                  (Var annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cz))
                  (Nop annz))
                  (Nop annz)))
                (Seq annz
                (Inst annz "F3able" (TypeD ["Int"],cz)
                  (FuncS annz "f3" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
                    (Seq annz
                    (Seq annz
                    (Var annz "v" (TypeV "Int",cz))
                    (Nop annz))
                    (Seq annz
                    (Set annz False (LVar "v") (Arg annz))
                    (Ret annz (Read annz "v"))))))
                (Ret annz (Call annz (Read annz "f3") (Number annz 10)))))
      `shouldBe`
        (Class'' annz "F3able" (cv "a")
          [(annz,"f3",(TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able")),False)]
        (Var'' annz "f3" (TypeF (TypeV "a") (TypeD ["Int"]),cvc("a","F3able"))
        (Seq annz
        (Nop annz)
        (Seq annz
        (Nop annz)
        (Inst'' annz "F3able" (TypeD ["Int"],cz)
          [(annz,"f3",(TypeF (TypeV "Int") (TypeD ["Int"]),cz),True)]
          (Var'' annz "$f3$(Int -> Int)$" (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
          (Match' annz False
            (LVar "$f3$(Int -> Int)$")
            (Func annz (TypeF (TypeV "Int") (TypeD ["Int"]),cz)
              (Var'' annz "v" (TypeV "Int",cz)
              (Seq annz
              (Nop annz)
              (Match' annz False (LVar "v") (Arg annz) (Seq annz (Nop annz) (Ret annz (Read annz "v"))) (Ret annz (Error annz (-2)))))))
            (Seq annz
              (Nop annz)
              (Ret annz (Call annz (Read annz "f3") (Number annz 10))))
            (Ret annz (Error annz (-2))))))))))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (Ret annz (Number annz 1))
      `shouldBe` Right (E.Number 1)

    it "data X with Int ; x:Int ; X 1 <- X 2" $ do
      go (Seq annz (Data annz ["Xxx"] [] (TypeD ["Int"],cz) False) (Seq annz (Set annz False (LCons ["Xxx"] (LNumber 1)) (Cons annz ["Xxx"] (Number annz 2))) (Ret annz (Number annz 2))))
      `shouldBe`
        Left ["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (Seq annz
          (CallS annz (Call annz
                        (Func annz (TypeF Type0 Type0,cz)
                          (Ret annz (Unit annz))) (Unit annz)))
          (Ret annz (Number annz 10)))
      `shouldBe` Right (E.Number 10)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (Ret annz
            (Call annz
              (Func annz (TypeF Type0 (TypeD ["Int"]),cz)
                (Ret annz (Number annz 10)))
              (Unit annz)))
      `shouldBe` Right (E.Number 10)
