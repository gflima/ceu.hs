module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval    as E
import Ceu.Full.Grammar
import Ceu.Full.Eval
import qualified Ceu.Full.Forever as Forever
import qualified Ceu.Full.Break   as Break
import qualified Ceu.Full.AndOr   as AndOr
import qualified Ceu.Full.Spawn   as Spawn
import qualified Ceu.Full.Async   as Async
import qualified Ceu.Full.Fin     as Fin
import qualified Ceu.Full.Trap    as Trap
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
  describe "Trap.compile" $ do

    it "trap escape;" $ do
      Trap.compile (Trap Nothing (Escape Nothing Nothing))
      `shouldBe` ([], (Trap' (Escape' 0)))

    it "trap/a escape/a;" $ do
      Trap.compile (Var "a" Nothing (Trap (Just "a") (Escape (Just "a") Nothing)))
      `shouldBe` ([], (Var "a" Nothing (Trap' (Escape' 0))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var "ret" Nothing (Trap (Just "ret") (Escape (Just "ret") (Just (Const 1)))))
      `shouldBe` ([], (Var "ret" Nothing (Trap' (Seq (Write "ret" (Const 1)) (Escape' 0)))))

    it "trap/a escape;" $ do
      Trap.compile (Var "ret" Nothing (Trap (Just "ret") (Escape Nothing Nothing)))
      `shouldBe` ([], (Var "ret" Nothing (Trap' (Escape' (-1)))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var "ret" Nothing (Trap (Just "ret") (Escape (Just "xxx") (Just (Const 1)))))
      `shouldBe` ([], (Var "ret" Nothing (Trap' (Escape' (-1)))))

    it "trap/a escape/a;" $ do
      compile' (False,False) (Var "ret" Nothing (Trap (Just "ret") (Escape (Just "xxx") (Just (Const 1)))))
      `shouldBe` (["trap: missing `escape` statement","escape: orphan `escape` statement"], (G.Var "ret" (G.Trap (G.Escape (-1)))))

  --------------------------------------------------------------------------
  describe "Fin.compile" $ do
    it "fin ..." $ do
      Fin.compile (Fin Nop Nop Nop)
      `shouldBe` (["finalize: unexpected `finalize`"],Or Nop (And Nop (Fin' Nop)))

    it "fin fin nop" $ do
      Fin.compile (Fin (Fin Nop Nop Nop) Nop Nop)
      `shouldBe` (["finalize: unexpected `finalize`","finalize: unexpected `finalize`"],Or Nop (And Nop (Fin' (Or Nop (And Nop (Fin' Nop))))))

    it "var x; fin x with nop; nop" $ do
      Fin.compile (Var "x" (Just (Nop,Nop,Nop)) Nop)
      `shouldBe` ([], (Var "x" Nothing (Or Nop (And Nop (Fin' Nop)))))

    it "var x; { fin x with nop; nop }" $ do
      Fin.compile (Var "x" (Just (Nop,Nop,Nop)) (Var "y" Nothing Nop))
      `shouldBe` ([], (Var "x" Nothing (Or (Var "y" Nothing Nop) (And Nop (Fin' Nop)))))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      Fin.compile (Var "x" (Just ((Write "x" (Const 1)),Nop,Nop)) (Var "y" Nothing (Seq (Fin (Write "x" (Const 2)) Nop Nop) (Write "x" (Const 3)))))
      `shouldBe` ([], (Var "x" Nothing (Or (Var "y" Nothing (Or (Write "x" (Const 3)) (And Nop (Fin' (Write "x" (Const 2)))))) (And Nop (Fin' (Write "x" (Const 1)))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      Fin.compile (Var "x" (Just (((Write "x" (Const 1)) `Seq` (Write "y" (Const 1))),Nop,Nop)) (Var "_" Nothing (Write "y" (Const 3))))
      `shouldBe` ([], (Var "x" Nothing (Or (Var "_" Nothing (Write "y" (Const 3))) (And Nop (Fin' (Seq (Write "x" (Const 1)) (Write "y" (Const 1))))))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      Fin.compile
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
        ([], (Var "x" Nothing
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
                    (And Nop (Fin' (Seq (Write "x" (Const 1)) (Seq (Write "y" (Const 1)) Nop)))))))

  --------------------------------------------------------------------------
  describe "Async.compile" $ do

    it "async { loop nop }" $ do
      Async.compile (Async (Loop Nop))
      `shouldBe` ([], (Loop (Seq Nop (AwaitExt "ASYNC" Nothing))))

  --------------------------------------------------------------------------
  describe "Spawn.compile" $ do

    it "spawn nop;" $ do
      Spawn.compile (Spawn Nop)
      `shouldBe` (["spawn: unexpected `spawn`"],Or (Clean' "Spawn" Nop) Nop)

    it "nop; spawn nop;" $ do
      Spawn.compile (Seq Nop (Spawn Nop))
      `shouldBe` (["spawn: unexpected `spawn`"],Seq Nop (Or (Clean' "Spawn" Nop) Nop))

    it "spawn nop; nop" $ do
      Spawn.compile (Seq (Spawn Nop) Nop)
      `shouldBe` ([], Or (Clean' "Spawn" Nop) Nop)

    it "spawn nop; nop" $ do
      compile' (False,False) (Seq (Spawn Nop) Nop)
      `shouldBe` (["terminating `spawn`"], G.Trap (G.Par (G.Seq G.Nop (G.AwaitExt "FOREVER")) (G.Seq G.Nop (G.Escape 0))))

    it "spawn awaitFor; nop" $ do
      Spawn.compile (Seq (Spawn AwaitFor) Nop)
      `shouldBe` ([], Or (Clean' "Spawn" AwaitFor) Nop)

  --------------------------------------------------------------------------
  describe "AndOr.compile" $ do

    it "(and nop nop)" $ do
      AndOr.compile (And Nop Nop) `shouldBe` ([], (Par' Nop Nop))
    it "(or nop awaitFor)" $ do
      AndOr.compile (Or Nop AwaitFor) `shouldBe` ([], (Clean' "Or" (Trap' (Par' (Seq Nop (Escape' 0)) (Seq AwaitFor (Escape' 0))))))
    it "(or nop awaitFor)" $ do
      (compile' (False,False) (Or Nop AwaitFor)) `shouldBe` ([], (G.Trap (G.Par (G.Seq G.Nop (G.Escape 0)) (G.AwaitExt "FOREVER"))))

  --------------------------------------------------------------------------
  describe "Break.compile" $ do

    it "loop (or break FOR)" $ do
      compile (Loop (Or Break AwaitFor))
      `shouldBe` ([], Clean' "Loop" (Trap' (Loop (Clean' "Or" (Trap' (Par' (Seq (Escape' 1) (Escape' 0)) (Seq (AwaitExt "FOREVER" Nothing) (Escape' 0))))))))

    it "loop (or break FOR)" $ do
      compile' (False,False) (Loop (Or Break AwaitFor))
      `shouldBe` (["loop: `loop` never iterates"], (G.Trap (G.Loop (G.Par (G.Escape 0) (G.AwaitExt "FOREVER")))))

    it "break" $ do
      Break.compile Break `shouldBe` ([], (Escape' (-1)))

    it "break" $ do
      compile' (False,False) Break `shouldBe` (["escape: orphan `escape` statement"], (G.Escape (-1)))

  --------------------------------------------------------------------------
  describe "Forever.compile" $ do

    it "await FOREVER;" $ do
      Forever.compile AwaitFor
      `shouldBe` ([], (AwaitExt "FOREVER" Nothing))

  --------------------------------------------------------------------------
  describe "compile'" $ do

    it "var x;" $ do
      compile' (False,False) (Var "x" Nothing Nop)
      `shouldBe` ([], (G.Var "x" G.Nop))
    it "var x;" $ do
      compile' (True,False) (Var "x" Nothing Nop)
      `shouldBe` ([], (G.Nop))

    it "do var x; x = 1 end" $ do
      compile' (False,False) (Var "x" Nothing (Write "x" (Const 1)))
      `shouldBe` ([], (G.Var "x" (G.Write "x" (Const 1))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      compile' (False,False) (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Var "x" Nothing AwaitFor)))
      `shouldBe` (["terminating `spawn`"], (G.Par (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Seq (G.AwaitExt "B") (G.Var "x" (G.AwaitExt "FOREVER")))))


    it "spawn do async ret++ end ;; await F;" $ do
      compile' (False,False) (Seq (Spawn (Async (Loop (Write "x" (Add (Read "x") (Const 1)))))) (AwaitExt "A" Nothing))
      `shouldBe` ([], (G.Trap (G.Par (G.Loop (G.Seq (G.Write "x" (Add (Read "x") (Const 1))) (G.AwaitExt "ASYNC"))) (G.Seq (G.AwaitExt "A") (G.Escape 0)))))

    it "trap terminates" $ do
      compile' (False,False) (Or (Trap' (Escape' 0)) AwaitFor)
      `shouldBe` ([], (G.Trap (G.Par (G.Seq (G.Trap (G.Escape 0)) (G.Escape 0)) (G.AwaitExt "FOREVER"))))

    it "removes unused trap" $ do
      compile' (False,False) (Seq (Fin Nop Nop Nop) AwaitFor)
      `shouldBe` ([], (G.Par (G.AwaitExt "FOREVER") (G.Par G.Nop (G.Fin G.Nop))))

    it "nested or/or/fin" $ do
      compile' (False,False)
        (Or
          AwaitFor
          (Or
            (Seq (Fin Nop Nop Nop) AwaitFor)
            Nop))
      `shouldBe`
        ([], G.Trap
          (G.Par
            (G.AwaitExt "FOREVER")
            (G.Seq
              (G.Trap
                (G.Par
                  (G.Par
                    (G.AwaitExt "FOREVER")
                    (G.Par G.Nop (G.Fin G.Nop)))
                  (G.Seq G.Nop (G.Escape 0))))
              (G.Escape 0))))

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
    evalFullProgItFail ["varsRead: undeclared variable: b"] [] (
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
    evalFullProgItSuccess (25,[[]]) [] (
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

    evalFullProgItSuccess (25,[[]]) []
      (Or
        (Loop (AwaitTmr (Const 5)))
        (Write "ret" (Const 25)))

  describe "events" $ do

{-
event int a;        // none
par/and do
    ret = await a;  // no ret
with
    emit a(10);     // no 10
end
-}
    evalFullProgItSuccess (10,[[]]) [] (
      Int "a" True (
        And
          (AwaitInt "a" (Just "ret"))
          (EmitInt "a" (Just (Const 10)))
      ))

    evalFullProgItFail ["varsWrite: undeclared variable: _a"] [] (
      Int "a" False (
        And
          (AwaitInt "a" (Just "ret"))
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItFail ["varsWrite: undeclared variable: _a"] [] (
      Int "a" False ( -- TODO: OK
        And
          (AwaitInt "a" Nothing)
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItSuccess (99,[[]]) [] (
      Int "a" False (
        And
          ((AwaitInt "a" Nothing) `Seq` (Write "ret" (Const 99)))
          (EmitInt "a" Nothing)
      ))
    evalFullProgItSuccess (99,[[]]) [] (
      Int "a" True (
        And
          ((AwaitInt "a" Nothing) `Seq` (Write "ret" (Const 99)))
          (EmitInt "a" (Just (Const 10)))
      ))
    evalFullProgItFail ["varsRead: uninitialized variable: _a"] [] (
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
    evalFullProgItFail ["varsRead: uninitialized variable: _A"] [("A",Nothing)] (
      Or
        (Every "A" (Just "ret") Nop)
        (AwaitExt "F" Nothing)
      )
    evalFullProgItSuccess (99,[[],[],[],[]]) [("A",Just 1),("A",Just 99),("F",Just 2)] (
      Or
        (Every "A" (Just "ret") Nop)
        (AwaitExt "F" Nothing)
      )

  describe "timers" $ do

    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 10)]
      (Seq (AwaitTmr (Const 10)) (Write "ret" (Const 10)))
    evalFullProgItFail ["pending inputs"] [("TIMER",Just 11)]
      (Seq (AwaitTmr (Const 10)) (Write "ret" (Const 10)))
    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)) `Seq` (Write "ret" (Const 10)))
    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Const 8)) `Seq` (AwaitTmr (Const 2)) `Seq` (Write "ret" (Const 10)))

    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          (AwaitTmr (Const 10))
          (AwaitTmr (Const 10)))
        (Write "ret" (Const 10)))

    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5))))
        (Write "ret" (Const 10)))

    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5))))
        (Seq
          (AwaitTmr (Const 10))
          (Write "ret" (Const 10))))

    evalFullProgItSuccess (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Const 5)) `Seq` (AwaitTmr (Const 5)))
          ((AwaitTmr (Const 4)) `Seq` (AwaitTmr (Const 5))))
        (Seq
          (AwaitTmr (Const 10))
          (Write "ret" (Const 10))))

    evalFullProgItSuccess
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

    evalFullProgItSuccess (1,[[],[("O",Just 1)],[("O",Just 2)],[]]) [("I",Just 1),("I",Just 2),("F",Nothing)]
      (Seq (Write "ret" (Const 1))
           (Var "i" Nothing
             (Or
               (AwaitExt "F" Nothing)
               (Every "I" (Just "i") (EmitExt "O" (Just (Read "i")))))))

  describe "pause" $ do

    evalFullProgItSuccess (99,[[]]) []
      (Int "x" True (Pause "x" (Write "ret" (Const 99))))

    evalFullProgItSuccess (99,[[]]) []
      (Or
        (Seq (AwaitExt "X" Nothing) (Write "ret" (Const 33)))
        (Int "x" True
          (Pause "x"
            (Seq
              (EmitInt "x" (Just (Const 1)))
              (Write "ret" (Const 99))))))

    evalFullProgItSuccess (99,[[],[],[],[],[]]) [("X",(Just 1)),("A",Nothing),("X",(Just 0)),("A",Nothing)]
      (Seq
        (Pause "X" (AwaitInt "A" Nothing))
        (Write "ret" (Const 99)))

    evalFullProgItSuccess (99,[[],[("P",Nothing)],[]]) [("X",Just 1),("E",Nothing)]
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
    evalFullProgItSuccess (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Seq (Fin (EmitExt "F" Nothing) (EmitExt "P" Nothing) (EmitExt "R" Nothing))
               (AwaitExt "E" Nothing)))
        (Write "ret" (Const 99)))

    evalFullProgItSuccess (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Var "x" (Just ((EmitExt "F" Nothing),(EmitExt "P" Nothing),(EmitExt "R" Nothing)))
            (AwaitExt "E" Nothing)))
        (Write "ret" (Const 99)))

      where
        evalFullProgItSuccess (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) res (show outss)) $
            (evalFullProg prog hist `shouldBe` E.Success (res,outss)))

        evalFullProgItFail err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) (show err)) $
            (evalFullProg prog hist) `shouldBe` E.Fail err)
