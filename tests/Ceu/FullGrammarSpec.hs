module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval         as E
import Ceu.Grammar.Full.Grammar
import Ceu.Grammar.Full.Eval
import qualified Ceu.Grammar.Full.Compile.Forever  as Forever
import qualified Ceu.Grammar.Full.Compile.Break    as Break
import qualified Ceu.Grammar.Full.Compile.ParAndOr as ParAndOr
import qualified Ceu.Grammar.Full.Compile.Spawn    as Spawn
import qualified Ceu.Grammar.Full.Compile.Async    as Async
import qualified Ceu.Grammar.Full.Compile.Fin      as Fin
import qualified Ceu.Grammar.Full.Compile.Trap     as Trap
import qualified Ceu.Grammar.Full.Compile.Scope    as Scope
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
  describe "Scope.compile" $ do

    it "var x" $ do
      Scope.compile (Var "x" Nothing)
      `shouldBe` ([], (Var' "x" Nothing Nop))

    it "var x; Nop" $ do
      Scope.compile (Seq (Var "x" Nothing) Nop)
      `shouldBe` ([], (Var' "x" Nothing Nop))

    it "var x <- 1 ; Nop" $ do
      Scope.compile (Seq (Var "x" Nothing) (Seq (Write "x" (Exp$Const 1)) Nop))
      `shouldBe` ([], (Var' "x" Nothing (Seq (Write "x" (Exp$Const 1)) Nop)))

    it "scope var x end ; var y" $ do
      Scope.compile (Seq (Scope (Var "x" Nothing)) (Var "y" Nothing))
      `shouldBe` ([],Seq (Var' "x" Nothing Nop) (Var' "y" Nothing Nop))

    it "scope var x end ; x=1" $ do
      compile' (False,False) (Seq (Scope (Var "x" Nothing)) (Write "x" (Exp$Const 1)))
      `shouldBe` (["assignment: variable 'x' is not declared"], G.Seq (G.Var "x" G.Nop) (G.Write "x" (Exp$Const 1)))

    it "var x" $ do
      compile' (False,True) (Var "x" Nothing)
      `shouldBe` (["trap: missing `escape` statement","await: unreachable statement"], G.Var "_ret" (G.Seq (G.Trap (G.Var "x" G.Nop)) (G.AwaitExt "FOREVER")))

    it "var x" $ do
      compile' (True,True) (Var "x" Nothing)
      `shouldBe` (["trap: missing `escape` statement","await: unreachable statement"], G.Var "_ret" (G.AwaitExt "FOREVER"))

    it "int x" $ do
      Scope.compile (Int "x" False)
      `shouldBe` ([], (Int' "x" False Nop))

    it "int x; Nop" $ do
      Scope.compile (Seq (Int "x" False) Nop)
      `shouldBe` ([], (Int' "x" False Nop))

    it "scope int x end ; int y" $ do
      Scope.compile (Seq (Scope (Int "x" False)) (Int "y" False))
      `shouldBe` ([],Seq (Int' "x" False Nop) (Int' "y" False Nop))

    it "scope int x end ; x=1" $ do
      compile' (False,False) (Seq (Scope (Int "x" False)) (EmitInt "x" Nothing))
      `shouldBe` (["emit: event 'x' is not declared"], G.Seq (G.Int "x" G.Nop) (G.EmitInt "x"))

    it "scope escape 1 end" $ do
      compile' (False,False) (Scope (Escape Nothing (Just (Exp$Const 1))))
      `shouldBe` (["escape: orphan `escape` statement"],G.Escape (-1))

    it "scope escape 1 end" $ do
      compile' (False,True) (Scope (Escape Nothing (Just (Exp$Const 1))))
      `shouldBe` ([],G.Var "_ret" (G.Seq (G.Trap (G.Seq (G.Write "_ret" (Exp$Const 1)) (G.Escape 0))) (G.AwaitExt "FOREVER")))

  --------------------------------------------------------------------------
  describe "Trap.compile" $ do

    it "trap escape;" $ do
      Trap.compile (Trap Nothing (Escape Nothing Nothing))
      `shouldBe` ([], (Trap' (Escape' (-1))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' "a" Nothing (Trap (Just "a") (Escape (Just "a") Nothing)))
      `shouldBe` ([], (Var' "a" Nothing (Trap' (Escape' 0))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' "ret" Nothing (Trap (Just "ret") (Escape (Just "ret") (Just (Exp$Const 1)))))
      `shouldBe` ([], (Var' "ret" Nothing (Trap' (Seq (Write "ret" (Exp$Const 1)) (Escape' 0)))))

    it "trap/a escape;" $ do
      Trap.compile (Var' "ret" Nothing (Trap (Just "ret") (Escape Nothing Nothing)))
      `shouldBe` ([], (Var' "ret" Nothing (Trap' (Escape' (-1)))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' "ret" Nothing (Trap (Just "ret") (Escape (Just "xxx") (Just (Exp$Const 1)))))
      `shouldBe` ([], (Var' "ret" Nothing (Trap' (Escape' (-1)))))

    it "trap/a escape/a;" $ do
      compile' (False,False) (Var' "ret" Nothing (Trap (Just "ret") (Escape (Just "xxx") (Just (Exp$Const 1)))))
      `shouldBe` (["trap: missing `escape` statement","escape: orphan `escape` statement"], (G.Var "ret" (G.Trap (G.Escape (-1)))))

  --------------------------------------------------------------------------
  describe "Fin.compile" $ do
    it "fin ..." $ do
      Fin.compile (Fin Nop Nop Nop)
      `shouldBe` (["finalize: unexpected `finalize`"],Or' Nop (Par AwaitFor (Fin' Nop)))

    it "fin fin nop" $ do
      Fin.compile (Fin (Fin Nop Nop Nop) Nop Nop)
      `shouldBe` (["finalize: unexpected `finalize`","finalize: unexpected `finalize`"],Or' Nop (Par AwaitFor (Fin' (Or' Nop (Par AwaitFor (Fin' Nop))))))

    it "var x; fin x with nop; nop" $ do
      Fin.compile (Var' "x" (Just (Nop,Nop,Nop)) Nop)
      `shouldBe` ([], (Var' "x" Nothing (Or' Nop (Par AwaitFor (Fin' Nop)))))

    it "var x; { fin x with nop; nop }" $ do
      Fin.compile (Var' "x" (Just (Nop,Nop,Nop)) (Var' "y" Nothing Nop))
      `shouldBe` ([], (Var' "x" Nothing (Or' (Var' "y" Nothing Nop) (Par AwaitFor (Fin' Nop)))))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      Fin.compile (Var' "x" (Just ((Write "x" (Exp$Const 1)),Nop,Nop)) (Var' "y" Nothing (Seq (Fin (Write "x" (Exp$Const 2)) Nop Nop) (Write "x" (Exp$Const 3)))))
      `shouldBe` ([], (Var' "x" Nothing (Or' (Var' "y" Nothing (Or' (Write "x" (Exp$Const 3)) (Par AwaitFor (Fin' (Write "x" (Exp$Const 2)))))) (Par AwaitFor (Fin' (Write "x" (Exp$Const 1)))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      Fin.compile (Var' "x" (Just (((Write "x" (Exp$Const 1)) `Seq` (Write "y" (Exp$Const 1))),Nop,Nop)) (Var' "_" Nothing (Write "y" (Exp$Const 3))))
      `shouldBe` ([], (Var' "x" Nothing (Or' (Var' "_" Nothing (Write "y" (Exp$Const 3))) (Par AwaitFor (Fin' (Seq (Write "x" (Exp$Const 1)) (Write "y" (Exp$Const 1))))))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      Fin.compile
        (Var' "x" (Just ((Write "x" (Exp$Const 1) `Seq` (Write "y" (Exp$Const 1)) `Seq` Nop),Nop,Nop))
                 (Seq Nop
                   (Seq
                     (Var' "_" Nothing (
                       (Fin (Write "x" (Exp$Const 2)) Nop Nop) `Seq`
                       (Write "x" (Exp$Const 3))               `Seq`
                       (Fin (Write "y" (Exp$Const 2)) Nop Nop) `Seq`
                       (Write "y" (Exp$Const 3))))
                     Nop)))
      `shouldBe`
        ([], (Var' "x" Nothing
                 (Or'
                   (Seq
                     Nop
                     (Seq
                       (Var' "_" Nothing
                         (Or'
                           (Seq
                             (Write "x" (Exp$Const 3))
                             (Or'
                               (Write "y" (Exp$Const 3))
                               (Par AwaitFor (Fin' (Write "y" (Exp$Const 2))))))
                           (Par AwaitFor (Fin' (Write "x" (Exp$Const 2))))))
                       Nop))
                    (Par AwaitFor (Fin' (Seq (Write "x" (Exp$Const 1)) (Seq (Write "y" (Exp$Const 1)) Nop)))))))

  --------------------------------------------------------------------------
  describe "Async.compile" $ do

    it "async { loop nop }" $ do
      Async.compile (Async (Loop Nop))
      `shouldBe` ([], (Loop (Seq Nop (AwaitExt "ASYNC" Nothing))))

  --------------------------------------------------------------------------
  describe "Spawn.compile" $ do

    it "spawn nop;" $ do
      Spawn.compile (Spawn Nop)
      `shouldBe` (["spawn: unexpected `spawn`"],Or' (Clean' "Spawn" Nop) Nop)

    it "nop; spawn nop;" $ do
      Spawn.compile (Seq Nop (Spawn Nop))
      `shouldBe` (["spawn: unexpected `spawn`"],Seq Nop (Or' (Clean' "Spawn" Nop) Nop))

    it "spawn nop; nop" $ do
      Spawn.compile (Seq (Spawn Nop) Nop)
      `shouldBe` ([], Or' (Clean' "Spawn" Nop) Nop)

    it "spawn nop; nop" $ do
      compile' (False,False) (Seq (Spawn Nop) Nop)
      `shouldBe` (["nop: terminating `spawn`"], G.Trap (G.Par (G.Seq G.Nop (G.AwaitExt "FOREVER")) (G.Seq G.Nop (G.Escape 0))))

    it "spawn awaitFor; nop" $ do
      Spawn.compile (Seq (Spawn AwaitFor) Nop)
      `shouldBe` ([], Or' (Clean' "Spawn" AwaitFor) Nop)

    it "spawn escape || escape" $ do
      compile' (False,False) (Trap (Just "a") (Seq (Spawn (Par (Escape Nothing (Just (Exp$Const 1))) (Escape (Just "a") Nothing))) Nop))
      `shouldBe` (["parallel: escaping `spawn`","escape: escaping statement","escape: escaping statement","assignment: variable 'a' is not declared"],G.Trap (G.Trap (G.Par (G.Par (G.Seq (G.Write "a" (Exp$Const 1)) (G.Escape 1)) (G.Escape 1)) (G.Seq G.Nop (G.Escape 0)))))

  --------------------------------------------------------------------------
  describe "ParAndOr.compile" $ do

    it "(and nop nop)" $ do
      ParAndOr.compile (And Nop Nop) `shouldBe` ([], (Trap' (Var' "__and" Nothing (Seq (Write "__and" (Exp$Const 0)) (Par' (Seq Nop (If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (Escape' 0) (Seq (Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) AwaitFor))) (Seq Nop (If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (Escape' 0) (Seq (Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) AwaitFor))))))))
    it "(or nop awaitFor)" $ do
      ParAndOr.compile (Or Nop AwaitFor) `shouldBe` ([], (Clean' "Or" (Trap' (Par' (Seq Nop (Escape' 0)) (Seq AwaitFor (Escape' 0))))))
    it "(or nop awaitFor)" $ do
      (compile' (False,False) (Or Nop AwaitFor)) `shouldBe` ([], (G.Trap (G.Par (G.Seq G.Nop (G.Escape 0)) (G.AwaitExt "FOREVER"))))
    it "(and nop (and nop nop))" $ do
      (compile' (False,False) (And Nop (And Nop Nop))) `shouldBe` ([],G.Trap (G.Var "__and" (G.Seq (G.Write "__and" (Exp$Const 0)) (G.Par (G.Seq G.Nop (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER")))) (G.Seq (G.Trap (G.Var "__and" (G.Seq (G.Write "__and" (Exp$Const 0)) (G.Par (G.Seq G.Nop (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER")))) (G.Seq G.Nop (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER")))))))) (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER"))))))))

  --------------------------------------------------------------------------
  describe "Break.compile" $ do

    it "loop (or break FOR)" $ do
      compile (Loop (Or Break AwaitFor))
      `shouldBe` ([], Clean' "Loop" (Trap' (Loop (Clean' "Or" (Trap' (Par' (Seq (Escape' 1) (Escape' 0)) (Seq (AwaitExt "FOREVER" Nothing) (Escape' 0))))))))

    it "loop (or break FOR)" $ do
      compile' (False,False) (Loop (Or Break AwaitFor))
      `shouldBe` (["trap: no trails terminate","loop: `loop` never iterates"], (G.Trap (G.Loop (G.Par (G.Escape 0) (G.AwaitExt "FOREVER")))))

    it "loop (par break FOR)" $ do
      compile' (False,False) (Loop (Par Break AwaitFor))
      `shouldBe` (["loop: `loop` never iterates"], (G.Trap (G.Loop (G.Par (G.Escape 0) (G.AwaitExt "FOREVER")))))

    it "loop (and break FOR)" $ do
      compile' (False,False) (Loop (And Break AwaitFor))
      `shouldBe` (["if: unreachable statement","if: unreachable statement"],G.Trap (G.Loop (G.Trap (G.Var "__and" (G.Seq (G.Write "__and" (Exp$Const 0)) (G.Par (G.Seq (G.Escape 1) (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER")))) (G.Seq (G.AwaitExt "FOREVER") (G.If (Exp$Equ (Exp$Read "__and") (Exp$Const 1)) (G.Escape 0) (G.Seq (G.Write "__and" (Exp$Add (Exp$Read "__and") (Exp$Const 1))) (G.AwaitExt "FOREVER"))))))))))

  --------------------------------------------------------------------------
  describe "Forever.compile" $ do

    it "await FOREVER;" $ do
      Forever.compile AwaitFor
      `shouldBe` ([], (AwaitExt "FOREVER" Nothing))

  --------------------------------------------------------------------------
  describe "compile'" $ do

    it "var x;" $ do
      compile' (False,False) (Var' "x" Nothing Nop)
      `shouldBe` ([], (G.Var "x" G.Nop))
    it "var x;" $ do
      compile' (True,False) (Var' "x" Nothing Nop)
      `shouldBe` ([], (G.Nop))

    it "do var x; x = 1 end" $ do
      compile' (False,False) (Var' "x" Nothing (Write "x" (Exp$Const 1)))
      `shouldBe` ([], (G.Var "x" (G.Write "x" (Exp$Const 1))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      compile' (False,False) (Seq (Spawn (AwaitExt "A" Nothing)) (Seq (AwaitExt "B" Nothing) (Var' "x" Nothing AwaitFor)))
      `shouldBe` (["await: terminating `spawn`"], (G.Par (G.Seq (G.AwaitExt "A") (G.AwaitExt "FOREVER")) (G.Seq (G.AwaitExt "B") (G.Var "x" (G.AwaitExt "FOREVER")))))

    it "spawn do async ret++ end ;; await F;" $ do
      compile' (False,False) (Seq (Spawn (Async (Loop (Write "x" (Exp$Add (Exp$Read "x") (Exp$Const 1)))))) (AwaitExt "A" Nothing))
      `shouldBe` (["assignment: variable 'x' is not declared","read access to 'x': variable 'x' is not declared"], (G.Trap (G.Par (G.Loop (G.Seq (G.Write "x" (Exp$Add (Exp$Read "x") (Exp$Const 1))) (G.AwaitExt "ASYNC"))) (G.Seq (G.AwaitExt "A") (G.Escape 0)))))

    it "trap terminates" $ do
      compile' (False,False) (Or (Trap' (Escape' 0)) AwaitFor)
      `shouldBe` ([], (G.Trap (G.Par (G.Seq (G.Trap (G.Escape 0)) (G.Escape 0)) (G.AwaitExt "FOREVER"))))

    it "removes unused trap" $ do
      compile' (False,False) (Seq (Fin Nop Nop Nop) AwaitFor)
      `shouldBe` ([], (G.Par (G.AwaitExt "FOREVER") (G.Par (G.AwaitExt "FOREVER") (G.Fin G.Nop))))

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
                    (G.Par (G.AwaitExt "FOREVER") (G.Fin G.Nop)))
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

    evalFullProgItRight (25,[[]]) []
      (Escape Nothing (Just (Exp$Const 25)))

    -- TODO: OK
    evalFullProgItRight (10,[[]]) [] (
      (Var' "a" (Just (Nop,Nop,Nop))
        (Escape Nothing (Just (Exp$Const 10)))
      ))

    -- TODO: OK
    evalFullProgItLeft ["read access to 'b': variable 'b' is not declared"] [] (
      (Var' "ret" Nothing (
      (Var' "a" (Just ((Write "ret" (Exp$Read "b")),Nop,Nop))
        (Var' "b" Nothing
          (Seq
            (Write "b" (Exp$Const 99))
            (Escape Nothing (Just (Exp$Const 0)))
          )
        )
      ))))

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
    evalFullProgItRight (25,[[]]) [] (
      (Int' "a" False (
      (Var' "ret" Nothing (
      (Write "ret" (Exp$Const 0)) `Seq`
      (Or
        ((AwaitInt "a" Nothing) `Seq` (Escape Nothing (Just (Exp$Add (Exp$Read "ret") (Exp$Const 5)))))
        (Or
          (
            (Fin (
              (Write "ret" (Exp$Mul (Exp$Read "ret") (Exp$Const 2))) `Seq`
              (EmitInt "a" Nothing)
            ) Nop Nop) `Seq`
            AwaitFor
          )
          (Write "ret" (Exp$Add (Exp$Read "ret") (Exp$Const 10)))
        )
      ))))))

    evalFullProgItLeft ["trap: no trails terminate"] []
      (Or
        (Loop (AwaitTmr (Exp$Const 5)))
        (Escape Nothing (Just (Exp$Const 25))))

    evalFullProgItLeft ["if: unreachable statement","if: unreachable statement"] []
      (And
        (Loop (AwaitTmr (Exp$Const 5)))
        (Escape Nothing (Just (Exp$Const 25))))

    evalFullProgItRight (25,[[]]) []
      (Par
        (Loop (AwaitTmr (Exp$Const 5)))
        (Escape Nothing (Just (Exp$Const 25))))

  describe "events" $ do

{-
event int a;        // none
par/and do
    ret = await a;  // no ret
with
    emit a(10);     // no 10
end
-}
    evalFullProgItRight (10,[[]]) [] (
      Int' "a" True (
        Par
          (Var' "ret" Nothing (Seq (AwaitInt "a" (Just "ret")) (Escape Nothing (Just (Exp$Read "ret")))))
          (EmitInt "a" (Just (Exp$Const 10)) `Seq` AwaitFor)
      ))

    evalFullProgItLeft ["read access to '_a': variable '_a' is not declared","assignment: variable '_a' is not declared"] []
      (Var' "ret" Nothing
        (Int' "a" False (
          Par
            (Seq (AwaitInt "a" (Just "ret")) (Escape Nothing (Just (Exp$Const 0))))
            (EmitInt "a" (Just (Exp$Const 10)) `Seq` AwaitFor))))

    evalFullProgItLeft ["assignment: variable '_a' is not declared"] [] (
      Int' "a" False
        (Seq
          (And
            (AwaitInt "a" Nothing)
            (EmitInt "a" (Just (Exp$Const 10))))
          (Escape Nothing (Just (Exp$Const 0)))))

    evalFullProgItRight (99,[[]]) [] (
      Int' "a" False (
        Par
          ((AwaitInt "a" Nothing) `Seq` (Escape Nothing (Just (Exp$Const 99))))
          (EmitInt "a" Nothing `Seq` AwaitFor)
      ))
    evalFullProgItRight (99,[[]]) [] (
      Int' "a" True (
        Par
          ((AwaitInt "a" Nothing) `Seq` (Escape Nothing (Just (Exp$Const 99))))
          (EmitInt "a" (Just (Exp$Const 10)) `Seq` AwaitFor)
      ))
    evalFullProgItLeft ["varsRead: uninitialized variable: _a"] []
      (Var' "ret" Nothing
        (Int' "a" True (
          Par
            (Seq (AwaitInt "a" (Just "ret")) (Escape Nothing (Just (Exp$Read "ret"))))
            (EmitInt "a" Nothing `Seq` AwaitFor))))

{-
par/or do
    every A in ret do end
with
    await F;
end
-}
    -- TODO: OK
    evalFullProgItLeft ["varsRead: uninitialized variable: _A"] [("A",Nothing)]
      (Var' "ret" Nothing
        (Seq
          (Or
            (Every "A" (Just "ret") Nop)
            (AwaitExt "F" Nothing))
          (Escape Nothing (Just (Exp$Read "ret")))))

    evalFullProgItRight (99,[[],[],[],[]]) [("A",Just 1),("A",Just 99),("F",Just 2)]
      (Var' "ret" Nothing
        (Par
          (Every "A" (Just "ret") Nop)
          (Seq (AwaitExt "F" Nothing) (Escape Nothing (Just (Exp$Read "ret"))))))

  describe "timers" $ do

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq (AwaitTmr (Exp$Const 10)) (Escape Nothing (Just (Exp$Const 10))))
    evalFullProgItLeft ["pending inputs"] [("TIMER",Just 11)]
      (Seq (AwaitTmr (Exp$Const 10)) (Escape Nothing (Just (Exp$Const 10))))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5)) `Seq` (Escape Nothing (Just (Exp$Const 10))))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr (Exp$Const 8)) `Seq` (AwaitTmr (Exp$Const 2)) `Seq` (Escape Nothing (Just (Exp$Const 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          (AwaitTmr (Exp$Const 10))
          (AwaitTmr (Exp$Const 10)))
        (Escape Nothing (Just (Exp$Const 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq
        (And
          ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5)))
          ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5))))
        (Escape Nothing (Just (Exp$Const 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5)))
          ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5))))
        (Seq
          (AwaitTmr (Exp$Const 10))
          (Escape Nothing (Just (Exp$Const 10)))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq
        (And
          ((AwaitTmr (Exp$Const 5)) `Seq` (AwaitTmr (Exp$Const 5)))
          ((AwaitTmr (Exp$Const 4)) `Seq` (AwaitTmr (Exp$Const 5))))
        (Seq
          (AwaitTmr (Exp$Const 10))
          (Escape Nothing (Just (Exp$Const 10)))))

    evalFullProgItRight
      (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])
      [("TIMER",Just 10),("TIMER",Just 11)]
      (Seq
        (And
          ((AwaitTmr (Exp$Const 5)) `Seq` (EmitExt "A" (Just (Exp$Const 1))) `Seq` (AwaitTmr (Exp$Const 5)) `Seq` (EmitExt "A" (Just (Exp$Const 2))))
          ((AwaitTmr (Exp$Const 4)) `Seq` (EmitExt "B" (Just (Exp$Const 1))) `Seq` (AwaitTmr (Exp$Const 7) `Seq` (EmitExt "B" (Just (Exp$Const 2))))))
        (
          (AwaitTmr (Exp$Const 10))          `Seq`
          (EmitExt "C" (Just (Exp$Const 1))) `Seq`
          (Escape Nothing (Just (Exp$Const 10)))))

  describe "outputs" $ do

    evalFullProgItRight (1,[[],[("O",Just 1)],[("O",Just 2)],[]]) [("I",Just 1),("I",Just 2),("F",Nothing)]
      (Var' "i" Nothing
        (Par
          (Seq (AwaitExt "F" Nothing) (Escape Nothing (Just (Exp$Const 1))))
          (Every "I" (Just "i") (EmitExt "O" (Just (Exp$Read "i"))))))

  describe "pause" $ do

    evalFullProgItRight (99,[[]]) []
      (Int' "x" True (Pause "x" (Escape Nothing (Just (Exp$Const 99)))))

    evalFullProgItRight (99,[[]]) []
      (Par
        (Seq (AwaitExt "X" Nothing) (Escape Nothing (Just (Exp$Const 33))))
        (Int' "x" True
          (Pause "x"
            (Seq
              (EmitInt "x" (Just (Exp$Const 1)))
              (Escape Nothing (Just (Exp$Const 99)))))))

    evalFullProgItRight (99,[[],[],[],[],[]]) [("X",(Just 1)),("A",Nothing),("X",(Just 0)),("A",Nothing)]
      (Seq
        (Pause "X" (AwaitExt "A" Nothing))
        (Escape Nothing (Just (Exp$Const 99))))

    evalFullProgItRight (99,[[],[("P",Nothing)],[]]) [("X",Just 1),("E",Nothing)]
      (Par
        (Pause "X"
          (Seq (Fin Nop (EmitExt "P" Nothing) Nop) AwaitFor))
        (Seq (AwaitExt "E" Nothing) (Escape Nothing (Just (Exp$Const 99)))))

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
    evalFullProgItRight (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Seq (Fin (EmitExt "F" Nothing) (EmitExt "P" Nothing) (EmitExt "R" Nothing))
               (AwaitExt "E" Nothing)))
        (Escape Nothing (Just (Exp$Const 99))))

    evalFullProgItRight (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]]) [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
      (Seq
        (Pause "X"
          (Var' "x" (Just ((EmitExt "F" Nothing),(EmitExt "P" Nothing),(EmitExt "R" Nothing)))
            (AwaitExt "E" Nothing)))
        (Escape Nothing (Just (Exp$Const 99))))

      where
        evalFullProgItRight (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) res (show outss)) $
            (evalFullProg prog hist `shouldBe` Right (res,outss)))

        evalFullProgItLeft err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) (show err)) $
            (evalFullProg prog hist) `shouldBe` Left err)
