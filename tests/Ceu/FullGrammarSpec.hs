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
  rnf Nop = ()
  rnf (Seq p q) = rnf p `seq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --describe "TODO" $ do
  --------------------------------------------------------------------------
  describe "remFin" $ do
    it "var x; fin x with nop; nop" $ do
      remFin (Var "x" (Seq (Fin (Just "x") Nop) Nop))
      `shouldBe` (Var "x" (Or (Fin' (Seq Nop Nop)) Nop))

    it "var x; { fin x with nop; nop }" $ do
      remFin (Var "x" (Var "y" (Seq (Fin (Just "x") Nop) Nop)))
      `shouldBe` (Var "x" (Or (Fin' (Seq Nop Nop)) (Var "y" Nop)))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      remFin (Var "x" (Var "y" (Seq (Fin (Just "x") (Write "x" (Const 1))) (Seq (Fin Nothing (Write "x" (Const 2))) (Write "x" (Const 3))))))
      `shouldBe` (Var "x" (Or (Fin' (Seq (Write "x" (Const 1)) Nop)) (Var "y" (Or (Fin' (Write "x" (Const 2))) (Write "x" (Const 3))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      remFin (Var "x" (Var "_" (
                (Fin (Just "x") (Write "x" (Const 1))) `Seq`
                (Fin (Just "x") (Write "y" (Const 1))) `Seq`
                (Write "y" (Const 3))
             )))
      `shouldBe` (Var "x" (Or (Fin' (Seq (Write "y" (Const 1)) (Seq (Write "x" (Const 1)) Nop))) (Var "_" (Write "y" (Const 3)))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      remFin (Var "x" (Seq Nop (Seq (Var "_" (
                (Fin (Just "x") (Write "x" (Const 1))) `Seq`
                (Fin Nothing    (Write "x" (Const 2))) `Seq`
                (Write "x" (Const 3))                  `Seq`
                (Fin (Just "x") (Write "y" (Const 1))) `Seq`
                (Fin Nothing    (Write "y" (Const 2))) `Seq`
                (Write "y" (Const 3))
             )) Nop)))
      `shouldBe` (Var "x" (Or (Fin' (Seq (Write "y" (Const 1)) (Seq (Write "x" (Const 1)) Nop))) (Seq Nop (Seq (Var "_" (Or (Fin' (Write "x" (Const 2))) (Seq (Write "x" (Const 3)) (Or (Fin' (Write "y" (Const 2))) (Write "y" (Const 3)))))) Nop))))

  --------------------------------------------------------------------------
  describe "remSpawn" $ do

    it "spawn nop;" $ do
      evaluate $ remSpawn (Spawn Nop)
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ remSpawn (Seq Nop (Spawn Nop))
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      remSpawn (Seq (Spawn Nop) Nop)
      `shouldBe` (Or (Seq Nop AwaitFor) Nop)

  --------------------------------------------------------------------------
  describe "chkSpawn" $ do

    it "spawn nop;" $ do
      forceEval $ chkSpawn (Spawn Nop)
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ chkSpawn (Seq Nop (Spawn Nop))
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      chkSpawn (Seq (Spawn Nop) Nop)
      `shouldBe` (Seq (Spawn Nop) Nop)

  --------------------------------------------------------------------------
  describe "remAsync" $ do

    it "async { loop nop }" $ do
      remAsync (Async (Loop Nop))
      `shouldBe` (Loop (Seq Nop (AwaitExt "ASYNC" Nothing)))

  --------------------------------------------------------------------------
  describe "remAwaitFor" $ do

    it "await FOREVER;" $ do
      remAwaitFor AwaitFor
      `shouldBe` (AwaitExt "FOREVER" Nothing)

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x" Nop)
      `shouldBe` (G.Var "x" G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Var "x" (Write "x" (Const 1)))
      `shouldBe` (G.Var "x" (G.Write "x" (Const 1)))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Var "x" AwaitFor)))
      `shouldBe` (G.Or (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Seq (G.AwaitExt "B") (G.Var "x" (G.AwaitExt "FOREVER"))))


    it "spawn do async ret++ end ;; await F;" $ do
      toGrammar (Seq (Spawn (Async (Loop (Write "x" (Add (Read "x") (Const 1)))))) (AwaitExt "A" Nothing))
      `shouldBe` (G.Or (G.Seq (G.Loop (G.Seq (G.Write "x" (Add (Read "x") (Const 1))) (G.AwaitExt "ASYNC"))) (G.AwaitExt "FOREVER")) (G.AwaitExt "A"))

  --------------------------------------------------------------------------
  describe "evalFullProg" $ do
    it "error \"Hello!\"" $ do
      evaluate $ evalFullProg (Error "Hello!") []
      `shouldThrow` errorCall "Runtime error: Hello!"

{-
var a;
var b = 1;
do finalize (a) with
    ret = b;
end
nop;
-}

    -- TODO-bug:
    -- `fin` is moved to be between "a" and "b", before "b" is defined,
    -- but `fin` uses "b".
    -- Solution is to reject variables in `fin` that are defined after "a"
    evalFullProgItPass (99,[[]]) [] (
      (Var "a"
        (Var "b"
          (Seq
            (Write "b" (Const 99))
            (Seq
              (Fin (Just "a") (Write "ret" (Read "b")))
              Nop
            )
          )
        )
      ))

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
    evalFullProgItPass (25,[[]]) [] (
      (Int "a" False (
      (Write "ret" (Const 0)) `Seq`
      (Or
        ((AwaitInt "a" Nothing) `Seq` (Write "ret" (Add (Read "ret") (Const 5))))
        (Or
          (
            (Fin Nothing (
              (Write "ret" (Mul (Read "ret") (Const 2))) `Seq`
              (EmitInt "a" Nothing)
            )) `Seq`
            AwaitFor
          )
          (Write "ret" (Add (Read "ret") (Const 10)))
        )
      ))))

  describe "events" $ do

{-
event int a;        // none
par/and do
    ret = await a;  // no ret
with
    emit a(10);     // no 10
end
-}
    evalFullProgItPass (10,[[]]) [] (
      Int "a" True (
        And
          (AwaitInt "a" (Just "ret"))
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItFail "varsWrite: undeclared variable: _a" [] (
      Int "a" False (
        And
          (AwaitInt "a" (Just "ret"))
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItFail "varsWrite: undeclared variable: _a" [] (
      Int "a" False ( -- TODO: OK
        And
          (AwaitInt "a" Nothing)
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItPass (99,[[]]) [] (
      Int "a" False (
        And
          ((AwaitInt "a" Nothing) `Seq` (Write "ret" (Const 99)))
          (EmitInt "a" Nothing)
      ))
    evalFullProgItPass (99,[[]]) [] (
      Int "a" True (
        And
          ((AwaitInt "a" Nothing) `Seq` (Write "ret" (Const 99)))
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItFail "varsRead: uninitialized variable: _a" [] (
      Int "a" True (
        And
          (AwaitInt "a" (Just "ret"))
          (EmitInt "a" Nothing)
      ))

{-
par/or do
    every A in ret do end
with
    await F;
end
-}
    evalFullProgItFail "varsRead: uninitialized variable: _A" [("A",Nothing)] (
      Or
        (Every "A" (Just "ret") Nop)
        (AwaitExt "F" Nothing)
      )
    evalFullProgItPass (99,[[],[],[],[]]) [("A",Just 1),("A",Just 99),("F",Just 2)] (
      Or
        (Every "A" (Just "ret") Nop)
        (AwaitExt "F" Nothing)
      )

  describe "timers" $ do

    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 10)]
      (Seq (AwaitTmr (Const 10)) (Write "ret" (Const 10)))
    evalFullProgItFail "evalProg: pending inputs" [("TIMER",Just 11)]
      (Seq (AwaitTmr (Const 10)) (Write "ret" (Const 10)))
    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)) `Seq` (Write "ret" (Const 10)))
    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Const 8)) `Seq` (AwaitTmr (Const 2)) `Seq` (Write "ret" (Const 10)))

    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          (AwaitTmr (Const 10))
          (AwaitTmr (Const 10)))
        (Write "ret" (Const 10)))

    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5))))
        (Write "ret" (Const 10)))

    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5))))
        (Seq
          (AwaitTmr (Const 10))
          (Write "ret" (Const 10))))

    evalFullProgItPass (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 4)) `Seq` (AwaitTmr (Const 5))))
        (Seq
          (AwaitTmr (Const 10))
          (Write "ret" (Const 10))))

    evalFullProgItPass
      (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])
      [("TIMER",Just 10),("TIMER",Just 11)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (EmitExt "A" (Just (Const 1))) `Seq` (AwaitTmr (Const 5)) `Seq` (EmitExt "A" (Just (Const 2))))
          ((AwaitTmr (Const 4)) `Seq` (EmitExt "B" (Just (Const 1))) `Seq` (AwaitTmr (Const 7) `Seq` (EmitExt "B" (Just (Const 2))))))
        (
          (AwaitTmr (Const 10))          `Seq`
          (EmitExt "C" (Just (Const 1))) `Seq`
          (Write "ret" (Const 10))))

  describe "outputs" $ do

    evalFullProgItPass (1,[[],[("O",Just 1)],[("O",Just 2)],[]]) [("I",Just 1),("I",Just 2),("F",Nothing)]
      (Seq (Write "ret" (Const 1))
           (Var "i"
             (Or
               (AwaitExt "F" Nothing)
               (Every "I" (Just "i") (EmitExt "O" (Just (Read "i")))))))

      where
        evalFullProgItPass (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg $ toGrammar prog) res (show outss)) $
            (evalFullProg prog hist `shouldBe` (res,outss)))

        evalFullProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg $ toGrammar prog) err) $
            (forceEval (evalFullProg prog hist) `shouldThrow` errorCall err))
