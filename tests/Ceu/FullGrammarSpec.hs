module Ceu.FullGrammarSpec (main, spec) where

import qualified Ceu.Grammar as G
import Ceu.FullGrammar
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "remVar" $ do

    it "var x;" $ do
      remVar (Var "x")
      `shouldBe` (["x"], Nop)

    it "x = 1;" $ do
      remVar (Write "x" (G.Const 1))
      `shouldBe` ([], Write "x" (G.Const 1))

    it "var x; x = 1" $ do
      remVar (Seq (Var "x") (Write "x" (G.Const 1)))
      `shouldBe` (["x"], Seq Nop (Write "x" (G.Const 1)))

    it "var x || x = 1" $ do
      remVar (Or (Var "x") (Write "x" (G.Const 1)))
      `shouldBe` (["x"], Or Nop (Write "x" (G.Const 1)))

    it "do var x; x = 1 end" $ do
      remVar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` ([], (Block' ["x"] (Seq Nop (Write "x" (G.Const 1)))))

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x")
      `shouldBe` G.Block ["ret","x"] (G.Seq G.Nop G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` G.Block ["ret"] (G.Seq G.Nop (G.Block ["x"] (G.Seq G.Nop (G.Write "x" (G.Const 1)))))

