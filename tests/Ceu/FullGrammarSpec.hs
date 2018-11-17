module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Globals
import qualified Ceu.Grammar as G
import Ceu.Full.Grammar
import Ceu.Full.Eval
import qualified Ceu.Full.Forever as Forever
import qualified Ceu.Full.Break   as Break
import qualified Ceu.Full.AndOr   as AndOr
import qualified Ceu.Full.Spawn   as Spawn
import qualified Ceu.Full.Async   as Async
import qualified Ceu.Full.Fin     as Fin
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
      Fin.remove (Var "x" (Just (Nop,Nop,Nop)) Nop)
      `shouldBe` (Var "x" Nothing (Or Nop (And Nop (Fin' Nop))))

    it "var x; { fin x with nop; nop }" $ do
      Fin.remove (Var "x" (Just (Nop,Nop,Nop)) (Var "y" Nothing Nop))
      `shouldBe` (Var "x" Nothing (Or (Var "y" Nothing Nop) (And Nop (Fin' Nop))))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      Fin.remove (Var "x" (Just ((Write "x" (Const 1)),Nop,Nop)) (Var "y" Nothing (Seq (Fin (Write "x" (Const 2)) Nop Nop) (Write "x" (Const 3)))))
      `shouldBe` (Var "x" Nothing (Or (Var "y" Nothing (Or (Write "x" (Const 3)) (And Nop (Fin' (Write "x" (Const 2)))))) (And Nop (Fin' (Write "x" (Const 1))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      Fin.remove (Var "x" (Just (((Write "x" (Const 1)) `Seq` (Write "y" (Const 1))),Nop,Nop)) (Var "_" Nothing (Write "y" (Const 3))))
      `shouldBe` (Var "x" Nothing (Or (Var "_" Nothing (Write "y" (Const 3))) (And Nop (Fin' (Seq (Write "x" (Const 1)) (Write "y" (Const 1)))))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      Fin.remove
        (Var "x" (Just ((Write "x" (Const 1) `Seq` (Write "y" (Const 1)) `Seq` Nop),Nop,Nop))
                 (Seq Nop
                   (Seq
                     (Var "_" Nothing (
                       (Fin (Write "x" (Const 2)) Nop Nop) `Seq`
                       (Write "x" (Const 3))               `Seq`
                       (Fin (Write "y" (Const 2)) Nop Nop) `Seq`
                       (Write "y" (Const 3))))
                     Nop)))
      `shouldBe`
        (Var "x" Nothing
                 (Or
                   (Seq
                     Nop
                     (Seq
                       (Var "_" Nothing
                         (Or
                           (Seq
                             (Write "x" (Const 3))
                             (Or
                               (Write "y" (Const 3))
                               (And Nop (Fin' (Write "y" (Const 2))))))
                           (And Nop (Fin' (Write "x" (Const 2))))))
                       Nop))
                    (And Nop (Fin' (Seq (Write "x" (Const 1)) (Seq (Write "y" (Const 1)) Nop))))))

  --------------------------------------------------------------------------
  describe "remSpawn" $ do

    it "spawn nop;" $ do
      evaluate $ Spawn.remove (Spawn Nop)
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ Spawn.remove (Seq Nop (Spawn Nop))
      `shouldThrow` errorCall "remSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      Spawn.remove (Seq (Spawn Nop) Nop)
      `shouldBe` (Or (Seq Nop AwaitFor) Nop)

  --------------------------------------------------------------------------
  describe "chkSpawn" $ do

    it "spawn nop;" $ do
      forceEval $ Spawn.check (Spawn Nop)
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "nop; spawn nop;" $ do
      forceEval $ Spawn.check (Seq Nop (Spawn Nop))
      `shouldThrow` errorCall "chkSpawn: unexpected statement (Spawn)"

    it "spawn nop; nop" $ do
      Spawn.check (Seq (Spawn Nop) Nop)
      `shouldBe` (Seq (Spawn Nop) Nop)

  --------------------------------------------------------------------------
  describe "remAsync" $ do

    it "async { loop nop }" $ do
      Async.remove (Async (Loop Nop))
      `shouldBe` (Loop (Seq Nop (AwaitExt "ASYNC" Nothing)))

  --------------------------------------------------------------------------
  describe "remBreak" $ do

    it "loop (or break FOR)" $ do
      Break.remove $ AndOr.remove (Loop (Or Break AwaitFor))
      `shouldBe` Trap' (Loop (Trap' (Par' (Seq (Escape' 1) (Escape' 0)) (Seq AwaitFor (Escape' 0)))))

  --------------------------------------------------------------------------
  describe "remAwaitFor" $ do

    it "await FOREVER;" $ do
      Forever.remove AwaitFor
      `shouldBe` (AwaitExt "FOREVER" Nothing)

  --------------------------------------------------------------------------
  describe "toGrammar" $ do

    it "var x;" $ do
      toGrammar (Var "x" Nothing Nop)
      `shouldBe` (G.Var "x" G.Nop)

    it "do var x; x = 1 end" $ do
      toGrammar (Var "x" Nothing (Write "x" (Const 1)))
      `shouldBe` (G.Var "x" (G.Write "x" (Const 1)))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      toGrammar (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Var "x" Nothing AwaitFor)))
      `shouldBe` (G.Trap (G.Par (G.Seq (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Escape 0)) (G.Seq (G.Seq (G.AwaitExt "B") (G.Var "x" (G.AwaitExt "FOREVER"))) (G.Escape 0))))


    it "spawn do async ret++ end ;; await F;" $ do
      toGrammar (Seq (Spawn (Async (Loop (Write "x" (Add (Read "x") (Const 1)))))) (AwaitExt "A" Nothing))
      `shouldBe` (G.Trap (G.Par (G.Seq (G.Seq (G.Trap (G.Loop (G.Seq (G.Write "x" (Add (Read "x") (Const 1))) (G.AwaitExt "ASYNC")))) (G.AwaitExt "FOREVER")) (G.Escape 0)) (G.Seq (G.AwaitExt "A") (G.Escape 0))))

  --------------------------------------------------------------------------
  describe "misc" $ do
    it "error \"Hello!\"" $ do
      evaluate $ evalFullProg (Error "Hello!") []
      `shouldThrow` errorCall "Runtime error: Hello!"

{-
var a;
do finalize (a) with
    ret = b;
end
var b = 1;
nop;
-}

    -- TODO: OK
    evalFullProgItFail "varsRead: undeclared variable: b" [] (
      (Var "a" (Just ((Write "ret" (Read "b")),Nop,Nop))
        (Var "b" Nothing
          (Seq
            (Write "b" (Const 99))
            Nop
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
            (Fin (
              (Write "ret" (Mul (Read "ret") (Const 2))) `Seq`
              (EmitInt "a" Nothing)
            ) Nop Nop) `Seq`
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

-- TODO
    --evalFullProgItPass (10,[[]]) [] Break
    --evalFullProgItFail "remBreak: `break` without `loop`" []
      --Break

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
    -- TODO: OK
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
           (Var "i" Nothing
             (Or
               (AwaitExt "F" Nothing)
               (Every "I" (Just "i") (EmitExt "O" (Just (Read "i")))))))

  describe "pause" $ do

    evalFullProgItPass (99,[[]]) []
      (Int "x" True (Pause "x" (Write "ret" (Const 99))))

    evalFullProgItPass (99,[[]]) []
      (Or
        (Seq (AwaitExt "X" Nothing) (Write "ret" (Const 33)))
        (Int "x" True
          (Pause "x"
            (Seq
              (EmitInt "x" (Just (Const 1)))
              (Write "ret" (Const 99))))))

    evalFullProgItPass (99,[[],[],[],[],[]]) [("X",(Just 1)),("A",Nothing),("X",(Just 0)),("A",Nothing)]
      (Seq
        (Pause "X" (AwaitInt "A" Nothing))
        (Write "ret" (Const 99)))

    evalFullProgItPass (99,[[],[("P",Nothing)],[]]) [("X",Just 1),("E",Nothing)]
      (Or
        (Pause "X"
          (Seq (Fin Nop (EmitExt "P" Nothing) Nop) AwaitFor))
        (Seq (AwaitExt "E" Nothing) (Write "ret" (Const 99))))

{-
pause/if X with
    do finalize with
        emit F;
    pause with
        emit P;
    resume with
        emit R;
    end
    await E;
end
-}
    evalFullProgItPass (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Seq (Fin (EmitExt "F" Nothing) (EmitExt "P" Nothing) (EmitExt "R" Nothing))
               (AwaitExt "E" Nothing)))
        (Write "ret" (Const 99)))

    evalFullProgItPass (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Var "x" (Just ((EmitExt "F" Nothing),(EmitExt "P" Nothing),(EmitExt "R" Nothing)))
            (AwaitExt "E" Nothing)))
        (Write "ret" (Const 99)))

      where
        evalFullProgItPass (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg $ toGrammar prog) res (show outss)) $
            (evalFullProg prog hist `shouldBe` (res,outss)))

        evalFullProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg $ toGrammar prog) err) $
            (forceEval (evalFullProg prog hist) `shouldThrow` errorCall err))
