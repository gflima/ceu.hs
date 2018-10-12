module Ceu.FullGrammarSpec (main, spec) where

import qualified Ceu.Grammar as G
import Ceu.FullGrammar
import Control.DeepSeq
import Control.Exception
import Test.Hspec

-- Declare Stmt as a datatype that can be fully evaluated.
instance NFData Stmt where
  rnf Nop' = ()
  rnf (Seq p q) = rnf p `seq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "remVar" $ do

    it "var x;" $ do
      evaluate $ remVar (Var "x")
      `shouldThrow` errorCall "remVar: expected enclosing top-level block"

    it "var x;" $ do
      remVar (Block (Var "x"))
      `shouldBe` (Block' ["x"] Nop')

    it "x = 1;" $ do
      remVar (Block (Write "x" (G.Const 1)))
      `shouldBe` (Block' [] (Write "x" (G.Const 1)))

    it "var x; x = 1" $ do
      remVar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` (Block' ["x"] (Seq Nop' (Write "x" (G.Const 1))))

    it "var x || x = 1" $ do
      remVar (Block (Or (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` (Block' ["x"] (Or Nop' (Write "x" (G.Const 1))))

    it "do var x; x = 1 end" $ do
      remVar (Block (Block (Seq (Var "x") (Write "x" (G.Const 1)))))
      `shouldBe` (Block' [] (Block' ["x"] (Seq Nop' (Write "x" (G.Const 1)))))

  --------------------------------------------------------------------------
  describe "remSpawn" $ do

    it "spawn nop;" $ do
      evaluate $ remSpawn (Spawn Nop')
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ remSpawn (Seq Nop' (Spawn Nop'))
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      remSpawn (Seq (Spawn Nop') Nop')
      `shouldBe` (Or (Seq Nop' AwaitFor) Nop')

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x")
      `shouldBe` G.Block ["ret","x"] (G.Seq G.Nop G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` G.Block ["ret"] (G.Seq G.Nop (G.Block ["x"] (G.Seq G.Nop (G.Write "x" (G.Const 1)))))

