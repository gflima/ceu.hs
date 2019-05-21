module Ceu.FullSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace

import Ceu.Grammar.Type     (Type(..))
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
      FuncS.compile (FuncS annz "id" (TypeF (TypeV "a" []) (TypeV "a" [])) (Nop annz))
      `shouldBe` (Seq annz
                  (Var' annz "id" False (TypeF (TypeV "a" []) (TypeV "a" [])))
                  (Set annz False (LVar "id")
                    (Func annz (TypeF (TypeV "a" []) (TypeV "a" [])) (Nop annz))))

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var' annz "x" False Type0)
        `shouldBe` (Var'' annz "x" False Type0 (Nop annz))

      it "var x; (Nop annz)" $ do
        Scope.compile (Seq annz (Var' annz "x" False Type0) (Nop annz))
        `shouldBe` (Var'' annz "x" False Type0 (Nop annz))

      it "var x <- 1 ; (Nop annz)" $ do
        Scope.compile (Seq annz (Var' annz "x" False (TypeD ["Int"])) (Seq annz (Set annz False (LVar "x") (Number annz 1)) (Nop annz)))
        `shouldBe` (Var'' annz "x" False (TypeD ["Int"]) (Seq annz (Set annz False (LVar "x") (Number annz 1)) (Nop annz)))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var' annz "x" False Type0)) (Var' annz "y" False Type0))
        `shouldBe` Seq annz (Var'' annz "x" False Type0 (Nop annz)) (Var'' annz "y" False Type0 (Nop annz))

      it "scope var x end ; x=1" $ do
        compile' (Seq annz (Scope annz (Var annz "x" (TypeD ["Int"]))) (Set annz False (LVar "x") (Number annz 1)))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared"], B.Seq annz (B.Var annz "x" False (TypeD ["Int"]) (B.Nop annz)) (B.Match annz False (B.LVar "x") (B.Number (annz{type_=TypeD ["Int","1"]}) 1) (B.Nop annz) (B.Ret annz (B.Error annz (-2)))))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (Var'' annz "x" False Type0 (Nop annz))
      `shouldBe` ([], (B.Var annz "x" False Type0 (B.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" False (TypeD ["Int"]) (Match' annz False (LVar "x") (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared"], (B.Var annz "x" False (TypeD ["Int"]) (B.Match annz False (B.LVar "x") (B.Number annz{type_=TypeD ["Int","1"]} 1) (B.Nop annz) (B.Nop annz))))

    it "do var x; x = 1 end" $ do
      compile' (Var'' annz "x" False (TypeD ["Int"]) (Match' annz False (LVar "x") (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` (["data 'Int' is not declared"], (B.Var annz "x" False (TypeD ["Int"]) (B.Match annz False (B.LVar "x") (B.Number annz{type_=TypeD ["Int","1"]} 1) (B.Nop annz) (B.Nop annz))))

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
      compile (Inst annz ("F3able",[TypeD ["Int"]])
                (FuncS annz "f3" (TypeF (TypeV "Int" []) (TypeD ["Int"]))
                  (Ret annz (Number annz 10))))
      `shouldBe`
        (Inst'' annz ("F3able",[TypeD ["Int"]])
          [(annz,"f3",TypeF (TypeV "Int" []) (TypeD ["Int"]),True)]
        (Var'' annz "$f3$(Int -> Int)$" False (TypeF (TypeV "Int" []) (TypeD ["Int"]))
          (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int" []) (TypeD ["Int"])) (Ret annz (Number annz 10))) (Nop annz) (Ret annz (Error annz (-2))))))

    it "class/inst/1" $ do
      compile (Seq annz
                (Class annz ("F3able",["a"]) []
                  (Var annz "f3" (TypeF (TypeV "a" []) (TypeD ["Int"]))))
                (Inst annz ("F3able",[TypeD ["Int"]])
                  (FuncS annz "f3" (TypeF (TypeV "Int" []) (TypeD ["Int"]))
                    (Ret annz (Number annz 10)))))
      `shouldBe`
        (Class'' annz ("F3able",["a"]) []
          [(annz,"f3",TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]),False)]
        (Var'' annz "f3" True (TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]))
        (Inst'' annz ("F3able",[TypeD ["Int"]])
          [(annz,"f3",TypeF (TypeV "Int" []) (TypeD ["Int"]),True)]
        (Var'' annz "$f3$(Int -> Int)$" False (TypeF (TypeV "Int" []) (TypeD ["Int"]))
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int" []) (TypeD ["Int"])) (Ret annz (Number annz 10))) (Nop annz) (Ret annz (Error annz (-2))))))))

    it "class/inst/2" $ do
      compile (Seq annz
                (Class annz ("F3able",["a"]) []
                  (Var annz "f3" (TypeF (TypeV "a" []) (TypeD ["Int"]))))
              (Seq annz
                (Inst annz ("F3able",[TypeD ["Int"]])
                  (FuncS annz "f3" (TypeF (TypeV "Int" []) (TypeD ["Int"]))
                    (Ret annz (Number annz 10))))
              (Ret annz (Call annz (Read annz "f3") (Number annz 10)))))
      `shouldBe`
        (Class'' annz ("F3able",["a"]) []
          [(annz,"f3",TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]),False)]
        (Var'' annz "f3" True (TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]))
        (Inst'' annz ("F3able",[TypeD ["Int"]])
          [(annz,"f3",TypeF (TypeV "Int" []) (TypeD ["Int"]),True)]
        (Var'' annz "$f3$(Int -> Int)$" False (TypeF (TypeV "Int" []) (TypeD ["Int"]))
            (Match' annz False (LVar "$f3$(Int -> Int)$") (Func annz (TypeF (TypeV "Int" []) (TypeD ["Int"])) (Ret annz (Number annz 10)))
              (Seq annz
                (Nop annz)
                (Ret annz (Call annz (Read annz "f3") (Number annz 10))))
              (Ret annz (Error annz (-2))))))))
    it "class/inst/3" $ do
      compile (Seq annz
                (Class annz ("F3able",["a"]) []
                  (Seq annz
                  (Seq annz
                  (Var annz "f3" (TypeF (TypeV "a" []) (TypeD ["Int"])))
                  (Nop annz))
                  (Nop annz)))
                (Seq annz
                (Inst annz ("F3able",[TypeD ["Int"]])
                  (FuncS annz "f3" (TypeF (TypeV "Int" []) (TypeD ["Int"]))
                    (Seq annz
                    (Seq annz
                    (Var annz "v" (TypeV "Int" []))
                    (Nop annz))
                    (Seq annz
                    (Set annz False (LVar "v") (Arg annz))
                    (Ret annz (Read annz "v"))))))
                (Ret annz (Call annz (Read annz "f3") (Number annz 10)))))
      `shouldBe`
        (Class'' annz ("F3able",["a"]) []
          [(annz,"f3",TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]),False)]
        (Var'' annz "f3" True (TypeF (TypeV "a" ["F3able"]) (TypeD ["Int"]))
        (Seq annz
        (Nop annz)
        (Seq annz
        (Nop annz)
        (Inst'' annz ("F3able",[TypeD ["Int"]])
          [(annz,"f3",TypeF (TypeV "Int" []) (TypeD ["Int"]),True)]
          (Var'' annz "$f3$(Int -> Int)$" False (TypeF (TypeV "Int" []) (TypeD ["Int"]))
          (Match' annz False
            (LVar "$f3$(Int -> Int)$")
            (Func annz (TypeF (TypeV "Int" []) (TypeD ["Int"]))
              (Var'' annz "v" False (TypeV "Int" [])
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
      go (Seq annz (Data annz ["Xxx"] [] (TypeD ["Int"]) False) (Seq annz (Set annz False (LCons ["Xxx"] (LNumber 1)) (Cons annz ["Xxx"] (Number annz 2))) (Ret annz (Number annz 2))))
      `shouldBe`
        Left ["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (Seq annz
          (CallS annz (Call annz
                        (Func annz (TypeF Type0 Type0)
                          (Ret annz (Unit annz))) (Unit annz)))
          (Ret annz (Number annz 10)))
      `shouldBe` Right (E.Number 10)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (Ret annz
            (Call annz
              (Func annz (TypeF Type0 (TypeD ["Int"]))
                (Ret annz (Number annz 10)))
              (Unit annz)))
      `shouldBe` Right (E.Number 10)
