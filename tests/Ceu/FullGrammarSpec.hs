module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Globals
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
  describe "remDcl" $ do

    it "var x;" $ do
      evaluate $ remDcl (Var "x")
      `shouldThrow` errorCall "remDcl: expected enclosing top-level block"

    it "evt x;" $ do
      evaluate $ remDcl (Evt "x")
      `shouldThrow` errorCall "remDcl: expected enclosing top-level block"

    it "var x;" $ do
      remDcl (Block (Var "x"))
      `shouldBe` (Block' (["x"],[]) Nop')

    it "x = 1;" $ do
      remDcl (Block (Write "x" (Const 1)))
      `shouldBe` (Block' ([],[]) (Write "x" (Const 1)))

    it "var x; x = 1" $ do
      remDcl (Block (Seq (Var "x") (Write "x" (Const 1))))
      `shouldBe` (Block' (["x"],[]) (Seq Nop' (Write "x" (Const 1))))

    it "var x || x = 1" $ do
      remDcl (Block (Or (Var "x") (Write "x" (Const 1))))
      `shouldBe` (Block' (["x"],[]) (Or Nop' (Write "x" (Const 1))))

    it "do var x; x = 1 end" $ do
      remDcl (Block (Block (Seq (Var "x") (Write "x" (Const 1)))))
      `shouldBe` (Block' ([],[]) (Block' (["x"],[]) (Seq Nop' (Write "x" (Const 1)))))

  --------------------------------------------------------------------------
  describe "remFin" $ do

    it "var x; fin x with nop; nop" $ do
      remFin (Block' (["x"],[]) (Seq (Fin (Just "x") Nop') Nop'))
      `shouldBe` (Block' (["x"],[]) (Or (Fin' (Seq Nop' Nop')) Nop'))

    it "var x; { fin x with nop; nop }" $ do
      remFin (Block' (["x"],[]) (Block' ([],[]) (Seq (Fin (Just "x") Nop') Nop')))
      `shouldBe` (Block' (["x"],[]) (Or (Fin' (Seq Nop' Nop')) (Block' ([],[]) Nop')))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      remFin (Block' (["x"],[]) (Block' ([],[]) (Seq (Fin (Just "x") (Write "x" (Const 1))) (Seq (Fin Nothing (Write "x" (Const 2))) (Write "x" (Const 3))))))
      `shouldBe` (Block' (["x"],[]) (Or (Fin' (Seq (Write "x" (Const 1)) Nop')) (Block' ([],[]) (Or (Fin' (Write "x" (Const 2))) (Write "x" (Const 3))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      remFin (Block' (["x"],[]) (Block' ([],[]) (
                (Fin (Just "x") (Write "x" (Const 1))) `Seq`
                (Fin (Just "x") (Write "y" (Const 1))) `Seq`
                (Write "y" (Const 3))
             )))
      `shouldBe` (Block' (["x"],[]) (Or (Fin' (Seq (Write "y" (Const 1)) (Seq (Write "x" (Const 1)) Nop'))) (Block' ([],[]) (Write "y" (Const 3)))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      remFin (Block' (["x"],[]) (Seq Nop' (Seq (Block' ([],[]) (
                (Fin (Just "x") (Write "x" (Const 1))) `Seq`
                (Fin Nothing    (Write "x" (Const 2))) `Seq`
                (Write "x" (Const 3))                  `Seq`
                (Fin (Just "x") (Write "y" (Const 1))) `Seq`
                (Fin Nothing    (Write "y" (Const 2))) `Seq`
                (Write "y" (Const 3))
             )) Nop')))
      `shouldBe` (Block' (["x"],[]) (Or (Fin' (Seq (Write "y" (Const 1)) (Seq (Write "x" (Const 1)) Nop'))) (Seq Nop' (Seq (Block' ([],[]) (Or (Fin' (Write "x" (Const 2))) (Seq (Write "x" (Const 3)) (Or (Fin' (Write "y" (Const 2))) (Write "y" (Const 3)))))) Nop'))))

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
      `shouldBe` (Loop (Seq Nop' (AwaitExt "ASYNC" Nothing)))

  --------------------------------------------------------------------------
  describe "remAwaitFor" $ do

    it "await FOREVER;" $ do
      remAwaitFor AwaitFor
      `shouldBe` (AwaitExt "FOREVER" Nothing)

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x")
      `shouldBe` (G.Block (["x"],[]) G.Nop)

    it "evt e;" $ do
      toGrammar (Evt "e")
      `shouldBe` (G.Block ([],["e"]) G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Block (Seq (Var "x") (Write "x" (Const 1))))
      `shouldBe` G.Block ([],[]) (G.Block (["x"],[]) (G.Seq G.Nop (G.Write "x" (Const 1))))

    it "do evt x; end" $ do
      toGrammar (Block (Evt "x"))
      `shouldBe` G.Block ([],[]) (G.Block ([],["x"]) G.Nop)

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Seq (Var "x") AwaitFor)))
      `shouldBe` (G.Block (["x"],[]) (G.Or (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Seq (G.AwaitExt "B") (G.Seq G.Nop (G.AwaitExt "FOREVER")))))

    it "spawn do await A; end ;; await B; evt x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Seq (Evt "x") AwaitFor)))
      `shouldBe` (G.Block ([],["x"]) (G.Or (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Seq (G.AwaitExt "B") (G.Seq G.Nop (G.AwaitExt "FOREVER")))))

    it "spawn do async x++ end ;; await F;" $ do
      toGrammar (Seq (Spawn (Async (Loop (Write "x" (Add (Read "x") (Const 1)))))) (AwaitExt "A" Nothing))
      `shouldBe` (G.Block ([],[]) (G.Or (G.Seq (G.Loop (G.Seq (G.Write "x" (Add (Read "x") (Const 1))) (G.AwaitExt "ASYNC"))) (G.AwaitExt "FOREVER")) (G.AwaitExt "A")))

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
      (Write "ret" (Const 0)) `Seq`
      (Or
        ((AwaitInt "e" Nothing) `Seq` (Write "ret" (Add (Read "ret") (Const 5))))
        (Or
          (
            (Fin Nothing (
              (Write "ret" (Mul (Read "ret") (Const 2))) `Seq`
              (EmitInt "e" (Const 0))
            )) `Seq`
            AwaitFor
          )
          (Write "ret" (Add (Read "ret") (Const 10)))
        )
      ))

    evalFullProgItPass 99 [("A",0),("B",99)]
      (Block ((Var "x") `Seq` ((AwaitExt "B" (Just "x")) `Seq` (EmitInt "x" (Read "x")))) `And` AwaitInt "x" (Just "ret"))

    evalFullProgItPass 33 [("A",11),("A",22),("B",0)]
      (
        (Write "ret" (Const 0)) `Seq`
        Block (Var "x" `Seq` (Or
            (Every "A" (Just "x") (Write "ret" (Add (Read "ret") (Read "x"))))
            (AwaitExt "B" Nothing))))

      where
        evalFullProgItPass res hist prog =
          (it (printf "pass: %s | %s ~>%d" (show hist) (G.showProg $ toGrammar prog) res) $
            (evalFullProg prog hist `shouldBe` res))
