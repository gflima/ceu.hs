module Ceu.SimplifySpec (main, spec) where

import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import Ceu.Grammar.Simplify
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "simplify" $ do
    it "Nop -> Nop" $ do
      simplify (Stmt Nop) `shouldBe` (Stmt Nop)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt Nop) (Stmt Nop))   `shouldBe` (Stmt Nop)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt Nop) (Stmt$Escape 0)) `shouldBe` (Stmt$Escape 0)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt$Escape 0) (Stmt Nop)) `shouldBe` (Stmt$Escape 0)
    it "Loop-Escape -> Nop" $ do
      simplify (Stmt$Loop (Stmt$Escape 0))    `shouldBe` (Stmt$Escape 0)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt$Seq (Stmt Nop) (Stmt$Escape 0)) (Stmt Nop)) `shouldBe` (Stmt$Escape 0)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt Nop) (Stmt$Seq (Stmt Nop) (Stmt$Escape 0))) `shouldBe` (Stmt$Escape 0)
    it "Seq -> Nop" $ do
      simplify (Stmt$Seq (Stmt Nop) (Stmt$Seq (Stmt Nop) (Stmt$Trap (Stmt$Escape 0)))) `shouldBe` (Stmt Nop)
    it "Break;* -> Break" $ do
      simplify (Stmt$Seq (Stmt$Escape 0) (Stmt$AwaitExt "")) `shouldBe` (Stmt$Escape 0)

    it "Var -> Nop" $ do
      simplify (Stmt$Var "" (Stmt Nop)) `shouldBe` (Stmt Nop)
    it "Var -> Break" $ do
      simplify (Stmt$Var "" (Stmt$Escape 0)) `shouldBe` (Stmt$Escape 0)
    it "Var -> Break" $ do
      simplify (Stmt$Var "" (Stmt$Seq (Stmt Nop) (Stmt$Escape 0))) `shouldBe` (Stmt$Escape 0)

    it "Int -> Nop" $ do
      simplify (Stmt$Int "" (Stmt Nop)) `shouldBe` (Stmt Nop)
    it "Int -> Break" $ do
      simplify (Stmt$Int "" (Stmt$Escape 0)) `shouldBe` (Stmt$Escape 0)
    it "Int -> Break" $ do
      simplify (Stmt$Int "" (Stmt$Seq (Stmt Nop) (Stmt$Escape 0))) `shouldBe` (Stmt$Escape 0)

    it "If a a -> a" $ do
      simplify (Stmt$If (Exp$Const 1) (Stmt$AwaitExt "") (Stmt$AwaitExt "")) `shouldBe` (Stmt$AwaitExt "")
    it "If x y -> Stmt$If x y" $ do
      simplify (Stmt$If (Exp$Const 1) (Stmt$Escape 0) (Stmt Nop)) `shouldBe` (Stmt$If (Exp$Const 1) (Stmt$Escape 0) (Stmt Nop))

    it "Every x y -> Every x y" $ do
      simplify (Stmt$Every "a" (Stmt$Escape 0)) `shouldBe` (Stmt$Every "a" (Stmt$Escape 0))

    it "Par Nop y -> y" $ do
      simplify (Stmt$Par (Stmt Nop) (Stmt$Seq (Stmt$Escape 0) (Stmt Nop))) `shouldBe` (Stmt$Escape 0)
    it "Par x Break -> Break" $ do
      simplify (Stmt$Par (Stmt$Seq (Stmt$Escape 0) (Stmt Nop)) (Stmt$AwaitExt "")) `shouldBe` (Stmt$Escape 0)
    it "Par x Break -> Break" $ do
      simplify (Stmt$Par (Stmt$Seq (Stmt$AwaitExt "") (Stmt Nop)) (Stmt$AwaitExt "")) `shouldBe` (Stmt$Par (Stmt$AwaitExt "") (Stmt$AwaitExt ""))

    it "Par Nop y -> y" $ do
      simplify (Stmt$Par (Stmt Nop) (Stmt$Seq (Stmt$Escape 0) (Stmt Nop))) `shouldBe` (Stmt$Escape 0)
    it "Par Break x -> Break" $ do
      simplify (Stmt$Par (Stmt$Seq (Stmt$Escape 0) (Stmt Nop)) (Stmt$AwaitExt "")) `shouldBe` (Stmt$Escape 0)
    it "Par x y -> Par x y" $ do
      simplify (Stmt$Par (Stmt$Seq (Stmt$AwaitExt "") (Stmt Nop)) (Stmt$AwaitExt "")) `shouldBe` (Stmt$Par (Stmt$AwaitExt "") (Stmt$AwaitExt ""))

    it "Pause -> Nop" $ do
      simplify (Stmt$Pause "" (Stmt Nop)) `shouldBe` (Stmt Nop)
    it "Pause -> Break" $ do
      simplify (Stmt$Pause "" (Stmt$Escape 0)) `shouldBe` (Stmt$Escape 0)
    it "Pause -> Break" $ do
      simplify (Stmt$Pause "" (Stmt$Seq (Stmt Nop) (Stmt$Escape 0))) `shouldBe` (Stmt$Escape 0)

    it "Fin -> Nop" $ do
      simplify (Stmt$Fin (Stmt$Var "" (Stmt$Trap (Stmt$Escape 0)))) `shouldBe` (Stmt Nop)
    it "Fin -> Nop" $ do
      simplify (Stmt$Fin (Stmt$Var "" (Stmt$If (Exp$Const 1) (Stmt Nop) (Stmt$Escape 0)))) `shouldBe` (Stmt$Fin (Stmt$Var "" (Stmt$If (Exp$Const 1) (Stmt Nop) (Stmt$Escape 0))))

    it "Trap Nop -> Nop" $ do
      simplify (Stmt$Trap (Stmt Nop)) `shouldBe` (Stmt Nop)
    it "Trap (Escape 0) -> Nop" $ do
      simplify (Stmt$Trap (Stmt$Escape 0)) `shouldBe` (Stmt Nop)
    it "Trap (Escape n) -> Escape n" $ do
      simplify (Stmt$Trap (Stmt$Escape 1)) `shouldBe` (Stmt$Escape 1)
    it "Trap p -> Trap p" $ do
      simplify (Stmt$Trap (Stmt$AwaitExt "")) `shouldBe` (Stmt$Trap (Stmt$AwaitExt ""))
