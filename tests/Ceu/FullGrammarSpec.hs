module Ceu.FullGrammarSpec (main, spec) where

import qualified Ceu.Grammar as G
import Ceu.FullGrammar
import Control.DeepSeq
import Control.Exception
import Test.Hspec
import Text.Printf

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
      `shouldBe` (Loop (Seq Nop' (AwaitExt inputAsync Nothing)))

  --------------------------------------------------------------------------
  describe "remAwaitFor" $ do

    it "await FOREVER;" $ do
      remAwaitFor AwaitFor
      `shouldBe` (AwaitExt G.inputForever Nothing)

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x")
      `shouldBe` (G.Block ["x"] G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Block (Seq (Var "x") (Write "x" (G.Const 1))))
      `shouldBe` G.Block [] (G.Block ["x"] (G.Seq G.Nop (G.Write "x" (G.Const 1))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt 0 Nothing)) (Seq (AwaitExt 1 Nothing) (Seq (Var "x") AwaitFor)))
      `shouldBe` (G.Block ["x"] (G.Or (G.Seq (G.AwaitExt 0 Nothing) (G.AwaitExt G.inputForever Nothing)) (G.Seq (G.AwaitExt 1 Nothing) (G.Seq G.Nop (G.AwaitExt G.inputForever Nothing)))))


    it "spawn do async ret++ end ;; await F;" $ do
      toGrammar (Seq (Spawn (Async (Loop (Write "x" (G.Add (G.Read "x") (G.Const 1)))))) (AwaitExt 0 Nothing))
      `shouldBe` (G.Block [] (G.Or (G.Seq (G.Loop (G.Seq (G.Write "x" (G.Add (G.Read "x") (G.Const 1))) (G.AwaitExt (-3) Nothing))) (G.AwaitExt (-2) Nothing)) (G.AwaitExt 0 Nothing)))

  --------------------------------------------------------------------------
  describe "evalFullProg" $ do
    it "error \"Hello!\"" $ do
      evaluate $ evalFullProg (Error "Hello!") []
      `shouldThrow` errorCall "Runtime error: Hello!"

{-
ret = 0;
par/or do
    await a;
    ret = ret + 5;          // 3- ret=25
with
    par/or do
        do finalize with
            ret = ret * 2;  // 2- ret=20
            emit a;         // (awakes par/or that could finalize again)
        end
        await FOREVER;
    with
        ret = ret + 10;     // 1- ret=10
    end
end
-}
    evalFullProgItPass 25 [] (
      (Write "ret" (G.Const 0)) `Seq`
      (Or
        ((AwaitInt 0 Nothing) `Seq` (Write "ret" (G.Add (G.Read "ret") (G.Const 5))))
        (Or
          (
            (Fin Nothing (
              (Write "ret" (G.Mul (G.Read "ret") (G.Const 2))) `Seq`
              (EmitInt 0 (G.Const 0))
            )) `Seq`
            AwaitFor
          )
          (Write "ret" (G.Add (G.Read "ret") (G.Const 10)))
        )
      ))

      where
        evalFullProgItPass res hist prog =
          (it (printf "pass: %s | %s ~>%d" (show hist) (G.showProg $ toGrammar prog) res) $
            (evalFullProg prog hist `shouldBe` res))
