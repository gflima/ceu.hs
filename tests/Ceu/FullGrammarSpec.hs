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
  describe "remFin" $ do

    it "var x; fin x with nop; nop" $ do
      remFin (Block' ["x"] (Seq (Fin (Just "x") Nop') Nop'))
      `shouldBe` (Block' ["x"] (Or (Fin' (Seq Nop' Nop')) Nop'))

    it "var x; { fin x with nop; nop }" $ do
      remFin (Block' ["x"] (Block' [] (Seq (Fin (Just "x") Nop') Nop')))
      `shouldBe` (Block' ["x"] (Or (Fin' (Seq Nop' Nop')) (Block' [] Nop')))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      remFin (Block' ["x"] (Block' [] (Seq (Fin (Just "x") (Write "x" (G.Const 1))) (Seq (Fin Nothing (Write "x" (G.Const 2))) (Write "x" (G.Const 3))))))
      `shouldBe` (Block' ["x"] (Or (Fin' (Seq (Write "x" (G.Const 1)) Nop')) (Block' [] (Or (Fin' (Write "x" (G.Const 2))) (Write "x" (G.Const 3))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      remFin (Block' ["x"] (Block' [] (
                (Fin (Just "x") (Write "x" (G.Const 1))) `Seq`
                (Fin (Just "x") (Write "y" (G.Const 1))) `Seq`
                (Write "y" (G.Const 3))
             )))
      `shouldBe` (Block' ["x"] (Or (Fin' (Seq (Write "y" (G.Const 1)) (Seq (Write "x" (G.Const 1)) Nop'))) (Block' [] (Write "y" (G.Const 3)))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      remFin (Block' ["x"] (Seq Nop' (Seq (Block' [] (
                (Fin (Just "x") (Write "x" (G.Const 1))) `Seq`
                (Fin Nothing    (Write "x" (G.Const 2))) `Seq`
                (Write "x" (G.Const 3))                  `Seq`
                (Fin (Just "x") (Write "y" (G.Const 1))) `Seq`
                (Fin Nothing    (Write "y" (G.Const 2))) `Seq`
                (Write "y" (G.Const 3))
             )) Nop')))
      `shouldBe` (Block' ["x"] (Or (Fin' (Seq (Write "y" (G.Const 1)) (Seq (Write "x" (G.Const 1)) Nop'))) (Seq Nop' (Seq (Block' [] (Or (Fin' (Write "x" (G.Const 2))) (Seq (Write "x" (G.Const 3)) (Or (Fin' (Write "y" (G.Const 2))) (Write "y" (G.Const 3)))))) Nop'))))

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
  describe "chkSpawn" $ do

    it "spawn nop;" $ do
      forceEval $ chkSpawn (Spawn Nop')
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ chkSpawn (Seq Nop' (Spawn Nop'))
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      chkSpawn (Seq (Spawn Nop') Nop')
      `shouldBe` (Seq (Spawn Nop') Nop')

  --------------------------------------------------------------------------
  describe "remAsync" $ do

    it "async { loop nop }" $ do
      remAsync (Async (Loop Nop'))
      `shouldBe` (Loop (Seq Nop' (AwaitExt inputAsync)))

  --------------------------------------------------------------------------
  describe "remAwaitFor" $ do

    it "await FOREVER;" $ do
      remAwaitFor AwaitFor
      `shouldBe` (AwaitExt inputForever)

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x")
      `shouldBe` G.Block ["ret","x"] (G.Seq G.Nop G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` G.Block ["ret"] (G.Seq G.Nop (G.Block ["x"] (G.Seq G.Nop (G.Write "x" (G.Const 1)))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt 0)) (Seq (AwaitExt 1) (Seq (Var "x") AwaitFor)))
      `shouldBe` (G.Block ["ret","x"] (G.Seq G.Nop (G.Or (G.Seq (G.AwaitExt 0) (G.AwaitExt inputForever)) (G.Seq (G.AwaitExt 1) (G.Seq G.Nop (G.AwaitExt inputForever))))))


    it "spawn do async ret++ end ;; await F;" $ do
      toGrammar (Seq (Spawn (Async (Loop (Write "x" (G.Add (G.Read "x") (G.Const 1)))))) (AwaitExt 0))
      `shouldBe` (G.Block ["ret"] (G.Seq G.Nop (G.Or (G.Seq (G.Loop (G.Seq (G.Write "x" (G.Add (G.Read "x") (G.Const 1))) (G.AwaitExt (-3)))) (G.AwaitExt (-2))) (G.AwaitExt 0))))
