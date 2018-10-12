module Ceu.FullGrammarSpec (main, spec) where

import Ceu.FullGrammar
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "remVars" $ do

    it "var x;" $ do
      remVars (Var "x")
      `shouldBe` (["x"], Nop)

    it "x = 1;" $ do
      remVars (Write "x" (Const 1))
      `shouldBe` ([], Write "x" (Const 1))

    it "var x; x = 1" $ do
      remVars (Seq (Var "x") (Write "x" (Const 1)))
      `shouldBe` (["x"], Seq Nop (Write "x" (Const 1)))

    it "var x || x = 1" $ do
      remVars (Or (Var "x") (Write "x" (Const 1)))
      `shouldBe` (["x"], Or Nop (Write "x" (Const 1)))

    it "do var x; x = 1 end" $ do
      remVars (Block (Seq (Var "x") (Write "x" (Const 1))))
      `shouldBe` ([], (Block' ["x"] (Seq Nop (Write "x" (Const 1)))))
