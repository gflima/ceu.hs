module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Grammar.Ann.Unit
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval         as E
import Ceu.Grammar.Full.Grammar
import Ceu.Grammar.Full.Eval
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
import Debug.Trace

-- Declare Stmt as a datatype that can be fully evaluated.
instance NFData (Stmt ann) where
  rnf (Nop _) = ()
  rnf (Seq _ p q) = rnf p `seq` rnf q

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

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var () "x" Nothing)
        `shouldBe` ([], (Var' () "x" Nothing (Nop ())))

      it "var x; (Nop ())" $ do
        Scope.compile (Seq () (Var () "x" Nothing) (Nop ()))
        `shouldBe` ([], (Var' () "x" Nothing (Nop ())))

      it "var x <- 1 ; (Nop ())" $ do
        Scope.compile (Seq () (Var () "x" Nothing) (Seq () (Write () "x" (Const () 1)) (Nop ())))
        `shouldBe` ([], (Var' () "x" Nothing (Seq () (Write () "x" (Const () 1)) (Nop ()))))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq () (Scope () (Var () "x" Nothing)) (Var () "y" Nothing))
        `shouldBe` ([],Seq () (Var' () "x" Nothing (Nop ())) (Var' () "y" Nothing (Nop ())))

      it "scope var x end ; x=1" $ do
        compile' (False,False) (Seq () (Scope () (Var () "x" Nothing)) (Write () "x" (Const () 1)))
        `shouldBe` (["assignment: identifier 'x' is not declared"], G.Seq () (G.Var () "x" (G.Nop ())) (G.Write () "x" (Const () 1)))

      it "var x" $ do
        compile' (False,True) (Var () "x" Nothing)
        `shouldBe` (["trap: terminating `trap` body","trap: missing `escape` statement","halt: unreachable statement"], G.Inp () "TIMER" (G.Var () "_ret" (G.Seq () (G.Trap () (G.Var () "x" (G.Nop ()))) (G.Halt ()))))

      it "var x" $ do
        compile' (True,True) (Var () "x" Nothing)
        `shouldBe` (["trap: terminating `trap` body","trap: missing `escape` statement","halt: unreachable statement"], G.Inp () "TIMER" (G.Var () "_ret" (G.Halt ())))

    describe "int:" $ do
      it "int x" $ do
        Scope.compile (Evt () "x" False)
        `shouldBe` ([], (Evt' () "x" False (Nop ())))

      it "int x; (Nop ())" $ do
        Scope.compile (Seq () (Evt () "x" False) (Nop ()))
        `shouldBe` ([], (Evt' () "x" False (Nop ())))

      it "scope int x end ; int y" $ do
        Scope.compile (Seq () (Scope () (Evt () "x" False)) (Evt () "y" False))
        `shouldBe` ([],Seq () (Evt' () "x" False (Nop ())) (Evt' () "y" False (Nop ())))

      it "scope int x end ; x=1" $ do
        compile' (False,False) (Seq () (Scope () (Evt () "x" False)) (EmitEvt () "x" Nothing))
        `shouldBe` (["emit: identifier 'x' is not declared"], G.Seq () (G.Evt () "x" (G.Nop ())) (G.EmitEvt () "x"))

    describe "output:" $ do
      it "output X" $ do
        Scope.compile (Out () "X" False)
        `shouldBe` ([], (Out' () "X" False (Nop ())))

      it "output X; (Nop ())" $ do
        Scope.compile (Seq () (Out () "X" False) (Nop ()))
        `shouldBe` ([], (Out' () "X" False (Nop ())))

      it "scope ext X end ; ext y" $ do
        Scope.compile (Seq () (Scope () (Out () "X" False)) (Out () "Y" False))
        `shouldBe` ([],Seq () (Out' () "X" False (Nop ())) (Out' () "Y" False (Nop ())))

      it "scope ext X end ; X=1" $ do
        compile' (False,False) (Seq () (Scope () (Out () "X" False)) (EmitEvt () "X" Nothing))
        `shouldBe` (["emit: identifier 'X' is not declared"], G.Seq () (G.Out () "X" (G.Nop ())) (G.EmitEvt () "X"))

      it "scope escape 1 end" $ do
        compile' (False,False) (Scope () (Escape () Nothing (Just (Const () 1))))
        `shouldBe` (["escape: orphan `escape` statement"],G.Escape () (-1))

      it "scope escape 1 end" $ do
        compile' (False,True) (Scope () (Escape () Nothing (Just (Const () 1))))
        `shouldBe` ([],G.Inp () "TIMER" (G.Var () "_ret" (G.Seq () (G.Trap () (G.Seq () (G.Write () "_ret" (Const () 1)) (G.Escape () 0))) (G.Halt ()))))

  --------------------------------------------------------------------------
  describe "Trap.compile" $ do

    it "trap escape;" $ do
      Trap.compile (Trap () Nothing (Escape () Nothing Nothing))
      `shouldBe` ([], (Trap' () (Escape' () (-1))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' () "a" Nothing (Trap () (Just "a") (Escape () (Just "a") Nothing)))
      `shouldBe` ([], (Var' () "a" Nothing (Trap' () (Escape' () 0))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' () "ret" Nothing (Trap () (Just "ret") (Escape () (Just "ret") (Just (Const () 1)))))
      `shouldBe` ([], (Var' () "ret" Nothing (Trap' () (Seq () (Write () "ret" (Const () 1)) (Escape' () 0)))))

    it "trap/a escape;" $ do
      Trap.compile (Var' () "ret" Nothing (Trap () (Just "ret") (Escape () Nothing Nothing)))
      `shouldBe` ([], (Var' () "ret" Nothing (Trap' () (Escape' () (-1)))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' () "ret" Nothing (Trap () (Just "ret") (Escape () (Just "xxx") (Just (Const () 1)))))
      `shouldBe` ([], (Var' () "ret" Nothing (Trap' () (Escape' () (-1)))))

    it "trap/a escape/a;" $ do
      compile' (False,False) (Var' () "ret" Nothing (Trap () (Just "ret") (Escape () (Just "xxx") (Just (Const () 1)))))
      `shouldBe` (["escape: orphan `escape` statement","trap: missing `escape` statement"], (G.Var () "ret" (G.Trap () (G.Escape () (-1)))))

  --------------------------------------------------------------------------
  describe "Fin.compile" $ do
    it "fin ..." $ do
      Fin.compile (Fin () (Nop ()) (Nop ()) (Nop ()))
      `shouldBe` (["finalize: unexpected `finalize`"],Or' () (Nop ()) (Par () (Halt ()) (Fin' () (Nop ()))))

    it "fin fin nop" $ do
      Fin.compile (Fin () (Fin () (Nop ()) (Nop ()) (Nop ())) (Nop ()) (Nop ()))
      `shouldBe` (["finalize: unexpected `finalize`","finalize: unexpected `finalize`"],Or' () (Nop ()) (Par () (Halt ()) (Fin' () (Or' () (Nop ()) (Par () (Halt ()) (Fin' () (Nop ())))))))

    it "var x; fin x with nop; nop" $ do
      Fin.compile (Var' () "x" (Just ((Nop ()),(Nop ()),(Nop ()))) (Nop ()))
      `shouldBe` ([], (Var' () "x" Nothing (Or' () (Nop ()) (Par () (Halt ()) (Fin' () (Nop ()))))))

    it "var x; { fin x with nop; nop }" $ do
      Fin.compile (Var' () "x" (Just ((Nop ()),(Nop ()),(Nop ()))) (Var' () "y" Nothing (Nop ())))
      `shouldBe` ([], (Var' () "x" Nothing (Or' () (Var' () "y" Nothing (Nop ())) (Par () (Halt ()) (Fin' () (Nop ()))))))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      Fin.compile (Var' () "x" (Just ((Write () "x" (Const () 1)),(Nop ()),(Nop ()))) (Var' () "y" Nothing (Seq () (Fin () (Write () "x" (Const () 2)) (Nop ()) (Nop ())) (Write () "x" (Const () 3)))))
      `shouldBe` ([], (Var' () "x" Nothing (Or' () (Var' () "y" Nothing (Or' () (Write () "x" (Const () 3)) (Par () (Halt ()) (Fin' () (Write () "x" (Const () 2)))))) (Par () (Halt ()) (Fin' () (Write () "x" (Const () 1)))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      Fin.compile (Var' () "x" (Just (((Write () "x" (Const () 1)) `sSeq` (Write () "y" (Const () 1))),(Nop ()),(Nop ()))) (Var' () "_" Nothing (Write () "y" (Const () 3))))
      `shouldBe` ([], (Var' () "x" Nothing (Or' () (Var' () "_" Nothing (Write () "y" (Const () 3))) (Par () (Halt ()) (Fin' () (Seq () (Write () "x" (Const () 1)) (Write () "y" (Const () 1))))))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      Fin.compile
        (Var' () "x" (Just ((Write () "x" (Const () 1) `sSeq` (Write () "y" (Const () 1)) `sSeq` (Nop ())),(Nop ()),(Nop ())))
                 (Seq () (Nop ())
                   (Seq ()
                     (Var' () "_" Nothing (
                       (Fin () (Write () "x" (Const () 2)) (Nop ()) (Nop ())) `sSeq`
                       (Write () "x" (Const () 3))               `sSeq`
                       (Fin () (Write () "y" (Const () 2)) (Nop ()) (Nop ())) `sSeq`
                       (Write () "y" (Const () 3))))
                     (Nop ()))))
      `shouldBe`
        ([], (Var' () "x" Nothing
                 (Or' ()
                   (Seq ()
                     (Nop ())
                     (Seq ()
                       (Var' () "_" Nothing
                         (Or' ()
                           (Seq ()
                             (Write () "x" (Const () 3))
                             (Or' ()
                               (Write () "y" (Const () 3))
                               (Par () (Halt ()) (Fin' () (Write () "y" (Const () 2))))))
                           (Par () (Halt ()) (Fin' () (Write () "x" (Const () 2))))))
                       (Nop ())))
                    (Par () (Halt ()) (Fin' () (Seq () (Write () "x" (Const () 1)) (Seq () (Write () "y" (Const () 1)) (Nop ()))))))))

  --------------------------------------------------------------------------
  describe "Async.compile" $ do

    it "async { loop nop }" $ do
      Async.compile (Async () (Loop () (Nop ())))
      `shouldBe` ([], (Loop () (Seq () (Nop ()) (AwaitInp () "ASYNC" Nothing))))

  --------------------------------------------------------------------------
  describe "Spawn.compile" $ do

    it "spawn nop;" $ do
      Spawn.compile (Spawn () (Nop ()))
      `shouldBe` (["spawn: unexpected `spawn`"],Or' () (Clean' () "Spawn" (Nop ())) (Nop ()))

    it "nop; spawn nop;" $ do
      Spawn.compile (Seq () (Nop ()) (Spawn () (Nop ())))
      `shouldBe` (["spawn: unexpected `spawn`"],Seq () (Nop ()) (Or' () (Clean' () "Spawn" (Nop ())) (Nop ())))

    it "spawn nop; nop" $ do
      Spawn.compile (Seq () (Spawn () (Nop ())) (Nop ()))
      `shouldBe` ([], Or' () (Clean' () "Spawn" (Nop ())) (Nop ()))

    it "spawn nop; nop" $ do
      compile' (False,False) (Seq () (Spawn () (Nop ())) (Nop ()))
      `shouldBe` (["nop: terminating `spawn`"], G.Trap () (G.Par () (G.Seq () (G.Nop ()) (G.Halt ())) (G.Seq () (G.Nop ()) (G.Escape () 0))))

    it "spawn awaitFor; nop" $ do
      Spawn.compile (Seq () (Spawn () (Halt ())) (Nop ()))
      `shouldBe` ([], Or' () (Clean' () "Spawn" (Halt ())) (Nop ()))

    it "spawn escape || escape" $ do
      compile' (False,False) (Trap () (Just "a") (Seq () (Spawn () (Par () (Escape () Nothing (Just (Const () 1))) (Escape () (Just "a") Nothing))) (Nop ())))
      `shouldBe` (["parallel: escaping `spawn`","escape: escaping statement","escape: escaping statement","trap: terminating `trap` body","assignment: identifier 'a' is not declared"],G.Trap () (G.Trap () (G.Par () (G.Par () (G.Seq () (G.Write () "a" (Const () 1)) (G.Escape () 1)) (G.Escape () 1)) (G.Seq () (G.Nop ()) (G.Escape () 0)))))

  --------------------------------------------------------------------------
  describe "ParAndOr.compile" $ do

    it "(and nop nop)" $ do
      ParAndOr.compile (And () (Nop ()) (Nop ())) `shouldBe` ([], (Clean' () "And" (Trap' () (Var' () "__and" Nothing (Seq () (Write () "__and" (Const () 0)) (Par' () (Seq () (Nop ()) (If () (Equ () (Read () "__and") (Const () 1)) (Escape' () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (Halt ())))) (Seq () (Nop ()) (If () (Equ () (Read () "__and") (Const () 1)) (Escape' () 0) (Seq () (Write () "__and" (Add () (Read () "__and") (Const () 1))) (Halt ()))))))))))
    it "(or nop awaitFor)" $ do
      ParAndOr.compile (Or () (Nop ()) (Halt ())) `shouldBe` ([], (Clean' () "Or" (Trap' () (Par' () (Seq () (Nop ()) (Escape' () 0)) (Seq () (Halt ()) (Escape' () 0))))))
    it "(or nop awaitFor)" $ do
      (compile' (False,False) (Or () (Nop ()) (Halt ()))) `shouldBe` ([], (G.Trap () (G.Par () (G.Seq () (G.Nop ()) (G.Escape () 0)) (G.Halt ()))))
    it "(and nop (and nop nop))" $ do
      (compile' (False,False) (And () (Nop ()) (And () (Nop ()) (Nop ())))) `shouldBe` ([], G.Seq () (G.Nop ()) (G.Seq () (G.Nop ()) (G.Nop ())))
    it "par for par for par for" $ do
      (compile' (True,False) (Par () (Halt ()) (Par () (Halt ()) (Halt ()))))
      `shouldBe` ([], G.Halt ())
    it "or nop or nop or for" $ do
      (compile' (True,False) (Or () (Nop ()) (Or () (Nop ()) (Halt ()))))
      `shouldBe` ([], G.Nop ())
    it "and nop and nop and nop" $ do
      (compile' (True,False) (And () (Nop ()) (And () (Nop ()) (Nop ()))))
      `shouldBe` ([], G.Nop ())
    it "(loop break) ; await X and nop" $ do
      (compile' (True,True) (And () (Seq () (Loop () (Break ())) (Seq () (Inp () "X" False) (AwaitInp () "X" Nothing))) (Nop ())))
      `shouldBe` (["trap: terminating `trap` body","trap: missing `escape` statement","loop: `loop` never iterates","halt: unreachable statement"], G.Inp () "TIMER" (G.Var () "_ret" (G.Seq () (G.Trap () (G.Trap () (G.Var () "__and" (G.Seq () (G.Write () "__and" (Const () 0)) (G.Par () (G.Seq () (G.Inp () "X" (G.AwaitInp () "X")) (G.If () (Equ () (Read () "__and") (Const () 1)) (G.Escape () 0) (G.Seq () (G.Write () "__and" (Add () (Read () "__and") (Const () 1))) (G.Halt ())))) (G.If () (Equ () (Read () "__and") (Const () 1)) (G.Escape () 0) (G.Seq () (G.Write () "__and" (Add () (Read () "__and") (Const () 1))) (G.Halt ())))))))) (G.Halt ()))))
    it "(loop break) ; await X and nop" $ do
      (compile' (False,True) (Seq () (And () (Seq () (Loop () (Break ())) (AwaitInp () "X" Nothing)) (Nop ())) (Escape () Nothing (Just (Const () 1))) ))
      `shouldBe` (["loop: `loop` never iterates","await: identifier 'X' is not declared"], G.Inp () "TIMER" (G.Var () "_ret" (G.Seq () (G.Trap () (G.Seq () (G.Trap () (G.Var () "__and" (G.Seq () (G.Write () "__and" (Const () 0)) (G.Par () (G.Seq () (G.Seq () (G.Trap () (G.Loop () (G.Escape () 0))) (G.AwaitInp () "X")) (G.If () (Equ () (Read () "__and") (Const () 1)) (G.Escape () 0) (G.Seq () (G.Write () "__and" (Add () (Read () "__and") (Const () 1))) (G.Halt ())))) (G.Seq () (G.Nop ()) (G.If () (Equ () (Read () "__and") (Const () 1)) (G.Escape () 0) (G.Seq () (G.Write () "__and" (Add () (Read () "__and") (Const () 1))) (G.Halt ())))))))) (G.Seq () (G.Write () "_ret" (Const () 1)) (G.Escape () 0)))) (G.Halt ()))))

  --------------------------------------------------------------------------
  describe "(Break ()).compile" $ do

    it "loop (or break FOR)" $ do
      compile (Loop () (Or () (Break ()) (Halt ())))
      `shouldBe` ([], Clean' () "Loop" (Trap' () (Loop () (Clean' () "Or" (Trap' () (Par' () (Seq () (Escape' () 1) (Escape' () 0)) (Seq () (Halt ()) (Escape' () 0))))))))

    it "loop (or break FOR)" $ do
      compile' (False,False) (Loop () (Or () (Break ()) (Halt ())))
      `shouldBe` (["trap: no trails terminate","loop: `loop` never iterates"], (G.Trap () (G.Loop () (G.Par () (G.Escape () 0) (G.Halt ())))))

    it "loop (par break FOR)" $ do
      compile' (False,False) (Loop () (Par () (Break ()) (Halt ())))
      `shouldBe` (["loop: `loop` never iterates"], (G.Trap () (G.Loop () (G.Par () (G.Escape () 0) (G.Halt ())))))

    it "loop (and break FOR)" $ do
      compile' (False,False) (Loop () (And () (Break ()) (Halt ())))
      `shouldBe` (["escape: trail must terminate","halt: trail must terminate","halt: unreachable statement","loop: `loop` never iterates"],G.Trap () (G.Loop () (G.Seq () (G.Escape () 0) (G.Halt ()))))

  --------------------------------------------------------------------------
{-
  describe "Forever.compile" $ do

    it "await FOREVER;" $ do
      Forever.compile (Halt ())
      `shouldBe` ([], (Halt ()))
-}

  --------------------------------------------------------------------------
  describe "compile'" $ do

    it "var x;" $ do
      compile' (False,False) (Var' () "x" Nothing (Nop ()))
      `shouldBe` ([], (G.Var () "x" (G.Nop ())))
    it "var x;" $ do
      compile' (True,False) (Var' () "x" Nothing (Nop ()))
      `shouldBe` ([], ((G.Nop ())))

    it "do var x; x = 1 end" $ do
      compile' (False,False) (Var' () "x" Nothing (Write () "x" (Const () 1)))
      `shouldBe` ([], (G.Var () "x" (G.Write () "x" (Const () 1))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      compile' (False,False) (Seq () (Inp () "A" False) (Seq () (Inp () "B" False) (Seq () (Spawn () (AwaitInp () "A" Nothing)) (Seq () (AwaitInp () "B" Nothing) (Var' () "x" Nothing (Halt ()))))))
      `shouldBe` (["await: terminating `spawn`"], G.Inp () "A" (G.Inp () "B" (G.Par () (G.Seq () (G.AwaitInp () "A") (G.Halt ())) (G.Seq () (G.AwaitInp () "B") (G.Var () "x" (G.Halt ()))))))

    it "spawn do async ret++ end ;; await F;" $ do
      compile' (False,False) (Seq () (Inp () "ASYNC" False) (Seq () (Inp () "A" False) (Seq () (Spawn () (Async () (Loop () (Write () "x" (Add () (Read () "x") (Const () 1)))))) (AwaitInp () "A" Nothing))))
      `shouldBe` (["assignment: identifier 'x' is not declared","read access to 'x': identifier 'x' is not declared"], G.Inp () "ASYNC" (G.Inp () "A" (G.Trap () (G.Par () (G.Loop () (G.Seq () (G.Write () "x" (Add () (Read () "x") (Const () 1))) (G.AwaitInp () "ASYNC"))) (G.Seq () (G.AwaitInp () "A") (G.Escape () 0))))))

    it "trap terminates" $ do
      compile' (False,False) (Or () (Trap' () (Escape' () 0)) (Halt ()))
      `shouldBe` ([], (G.Trap () (G.Par () (G.Seq () (G.Trap () (G.Escape () 0)) (G.Escape () 0)) (G.Halt ()))))

    it "removes unused trap" $ do
      compile' (False,False) (Seq () (Fin () (Nop ()) (Nop ()) (Nop ())) (Halt ()))
      `shouldBe` ([], G.Par () (G.Halt ()) (G.Par () (G.Halt ()) (G.Fin () (G.Nop ()))))

    it "nested or/or/fin" $ do
      compile' (False,False)
        (Or ()
          (Halt ())
          (Or ()
            (Seq () (Fin () (Nop ()) (Nop ()) (Nop ())) (Halt ()))
            (Nop ())))
      `shouldBe`
        ([], G.Trap ()
          (G.Par ()
            (G.Halt ())
            (G.Seq ()
              (G.Trap ()
                (G.Par ()
                  (G.Par ()
                    (G.Halt ())
                    (G.Par () (G.Halt ()) (G.Fin () (G.Nop ()))))
                  (G.Seq () (G.Nop ()) (G.Escape () 0))))
              (G.Escape () 0))))

  --------------------------------------------------------------------------
  describe "misc" $ do
    it "error \"Hello!\"" $ do
      evaluate $ evalFullProg (Error () "Hello!") []
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
      (Escape () Nothing (Just (Const () 25)))

    -- TODO: OK
    evalFullProgItRight (10,[[]]) [] (
      (Var' () "a" (Just ((Nop ()),(Nop ()),(Nop ())))
        (Escape () Nothing (Just (Const () 10)))
      ))

    -- TODO: OK
    evalFullProgItLeft ["read access to 'b': identifier 'b' is not declared"] [] (
      (Var' () "ret" Nothing (
      (Var' () "a" (Just ((Write () "ret" (Read () "b")),(Nop ()),(Nop ())))
        (Var' () "b" Nothing
          (Seq ()
            (Write () "b" (Const () 99))
            (Escape () Nothing (Just (Const () 0)))
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
      (Evt' () "a" False (
      (Var' () "ret" Nothing (
      (Write () "ret" (Const () 0)) `sSeq`
      (Par ()
        ((AwaitEvt () "a" Nothing) `sSeq` (Escape () Nothing (Just (Add () (Read () "ret") (Const () 5)))))
        (Seq ()
          (Or ()
            (
              (Fin () (
                (Write () "ret" (Mul () (Read () "ret") (Const () 2))) `sSeq`
                (EmitEvt () "a" Nothing)
              ) (Nop ()) (Nop ())) `sSeq`
              (Halt ())
            )
            (Write () "ret" (Add () (Read () "ret") (Const () 10)))
          )
          (Halt ()))
      ))))))

    evalFullProgItLeft ["trap: no trails terminate"] []
      (Or ()
        (Loop () (AwaitTmr () (Const () 5)))
        (Escape () Nothing (Just (Const () 25))))

    evalFullProgItLeft ["loop: trail must terminate","sequence: trail must terminate","trap: terminating `trap` body","if: unreachable statement","if: unreachable statement"] []
      (And ()
        (Loop () (AwaitTmr () (Const () 5)))
        (Escape () Nothing (Just (Const () 25))))

    evalFullProgItRight (25,[[]]) []
      (Par ()
        (Loop () (AwaitTmr () (Const () 5)))
        (Escape () Nothing (Just (Const () 25))))

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
      Evt' () "a" True (
        Par ()
          (Var' () "ret" Nothing (Seq () (AwaitEvt () "a" (Just "ret")) (Escape () Nothing (Just (Read () "ret")))))
          (EmitEvt () "a" (Just (Const () 10)) `sSeq` (Halt ()))
      ))

    evalFullProgItLeft ["read access to '_a': identifier '_a' is not declared","assignment: identifier '_a' is not declared"] []
      (Var' () "ret" Nothing
        (Evt' () "a" False (
          Par ()
            (Seq () (AwaitEvt () "a" (Just "ret")) (Escape () Nothing (Just (Const () 0))))
            (EmitEvt () "a" (Just (Const () 10)) `sSeq` (Halt ())))))

    evalFullProgItLeft ["assignment: identifier '_a' is not declared"] [] (
      Evt' () "a" False
        (Seq ()
          (And ()
            (AwaitEvt () "a" Nothing)
            (EmitEvt () "a" (Just (Const () 10))))
          (Escape () Nothing (Just (Const () 0)))))

    evalFullProgItRight (99,[[]]) [] (
      Evt' () "a" False (
        Par ()
          ((AwaitEvt () "a" Nothing) `sSeq` (Escape () Nothing (Just (Const () 99))))
          (EmitEvt () "a" Nothing `sSeq` (Halt ()))
      ))
    evalFullProgItRight (99,[[]]) [] (
      Evt' () "a" True (
        Par ()
          ((AwaitEvt () "a" Nothing) `sSeq` (Escape () Nothing (Just (Const () 99))))
          (EmitEvt () "a" (Just (Const () 10)) `sSeq` (Halt ()))
      ))
    evalFullProgItLeft ["varsRead: uninitialized variable: _a"] []
      (Var' () "ret" Nothing
        (Evt' () "a" True (
          Par ()
            (Seq () (AwaitEvt () "a" (Just "ret")) (Escape () Nothing (Just (Read () "ret"))))
            (EmitEvt () "a" Nothing `sSeq` (Halt ())))))

{-
par/or do
    every A in ret do end
with
    await F;
end
-}
    -- TODO: OK
    evalFullProgItLeft ["varsRead: uninitialized variable: _A"] [("A",Nothing)]
      (Seq () (Inp () "F" False)
      (Seq () (Inp () "A" False)
      (Var' () "ret" Nothing
        (Seq ()
          (Or ()
            (Every () "A" (Just "ret") (Nop ()))
            (AwaitInp () "F" Nothing))
          (Escape () Nothing (Just (Read () "ret")))))))

    evalFullProgItRight (99,[[],[],[],[]]) [("A",Just 1),("A",Just 99),("F",Just 2)]
      (Seq () (Inp () "A" True)
      (Seq () (Inp () "F" True)
      (Var' () "ret" Nothing
        (Par ()
          (Every () "A" (Just "ret") (Nop ()))
          (Seq () (AwaitInp () "F" Nothing) (Escape () Nothing (Just (Read () "ret"))))))))

  describe "timers" $ do

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq () (AwaitTmr () (Const () 10)) (Escape () Nothing (Just (Const () 10))))
    evalFullProgItLeft ["pending inputs"] [("TIMER",Just 11)]
      (Seq () (AwaitTmr () (Const () 10)) (Escape () Nothing (Just (Const () 10))))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5)) `sSeq` (Escape () Nothing (Just (Const () 10))))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr () (Const () 8)) `sSeq` (AwaitTmr () (Const () 2)) `sSeq` (Escape () Nothing (Just (Const () 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq ()
        (And ()
          (AwaitTmr () (Const () 10))
          (AwaitTmr () (Const () 10)))
        (Escape () Nothing (Just (Const () 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq ()
        (And ()
          ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5)))
          ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5))))
        (Escape () Nothing (Just (Const () 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq ()
        (And ()
          ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5)))
          ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5))))
        (Seq ()
          (AwaitTmr () (Const () 10))
          (Escape () Nothing (Just (Const () 10)))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq ()
        (And ()
          ((AwaitTmr () (Const () 5)) `sSeq` (AwaitTmr () (Const () 5)))
          ((AwaitTmr () (Const () 4)) `sSeq` (AwaitTmr () (Const () 5))))
        (Seq ()
          (AwaitTmr () (Const () 10))
          (Escape () Nothing (Just (Const () 10)))))

    evalFullProgItRight
      (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])
      [("TIMER",Just 10),("TIMER",Just 11)]
      (Seq () (Inp () "A" False) (Seq () (Inp () "B" False) (Seq () (Inp () "C" True) (Seq ()
        (And ()
          ((AwaitTmr () (Const () 5)) `sSeq` (EmitExt () "A" (Just (Const () 1))) `sSeq` (AwaitTmr () (Const () 5)) `sSeq` (EmitExt () "A" (Just (Const () 2))))
          ((AwaitTmr () (Const () 4)) `sSeq` (EmitExt () "B" (Just (Const () 1))) `sSeq` (AwaitTmr () (Const () 7) `sSeq` (EmitExt () "B" (Just (Const () 2))))))
        (
          (AwaitTmr () (Const () 10))          `sSeq`
          (EmitExt () "C" (Just (Const () 1))) `sSeq`
          (Escape () Nothing (Just (Const () 10))))))))

    it "xxx" $
        evalFullProg
            (Seq ()
                ((Out () "A" True) `sSeq` (Out () "B" True) `sSeq` (Out () "C" True))
                (Seq ()
                    (And ()
                        ((AwaitTmr () (Const () 5))             `sSeq`
                        (EmitExt () "A" (Just (Const () 1)))    `sSeq`
                        (AwaitTmr () (Const () 5))              `sSeq`
                        (EmitExt () "A" (Just (Const () 2))))

                        ((AwaitTmr () (Const () 4))             `sSeq`
                        (EmitExt () "B" (Just (Const () 1)))    `sSeq`
                        (AwaitTmr () (Const () 7)               `sSeq`
                        (EmitExt () "B" (Just (Const () 2))))))
                    (
                        (AwaitTmr () (Const () 10))          `sSeq`
                        (EmitExt () "C" (Just (Const () 1))) `sSeq`
                        (Escape () Nothing (Just (Const () 10))))))
            [("TIMER",Just 10),("TIMER",Just 11)]
        `shouldBe` Right (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])

  describe "outputs" $ do

    evalFullProgItRight (1,[[],[("O",Just 1)],[("O",Just 2)],[]]) [("I",Just 1),("I",Just 2),("F",Nothing)]
      (Seq () ((Inp () "I" True) `sSeq` (Inp () "F" False) `sSeq` (Out () "O" True)) (Var' () "i" Nothing
        (Par ()
          (Seq () (AwaitInp () "F" Nothing) (Escape () Nothing (Just (Const () 1))))
          (Every () "I" (Just "i") (EmitExt () "O" (Just (Read () "i")))))))

  describe "pause" $ do

    evalFullProgItRight (99,[[]]) []
      (Evt' () "x" True (Pause () "x" (Escape () Nothing (Just (Const () 99)))))

    evalFullProgItRight (99,[[]]) []
      (Seq () ((Inp () "X" True) `sSeq` (Inp () "A" False)) (Par ()
        (Seq () (AwaitInp () "X" Nothing) (Escape () Nothing (Just (Const () 33))))
        (Evt' () "x" True
          (Pause () "x"
            (Seq ()
              (EmitEvt () "x" (Just (Const () 1)))
              (Escape () Nothing (Just (Const () 99))))))))

    evalFullProgItRight (99,[[],[],[],[],[]]) [("X",(Just 1)),("A",Nothing),("X",(Just 0)),("A",Nothing)]
      (Seq () ((Inp () "X" True) `sSeq` (Inp () "A" False)) (Seq ()
        (Pause () "X" (AwaitInp () "A" Nothing))
        (Escape () Nothing (Just (Const () 99)))))

    evalFullProgItRight (99,[[],[("P",Nothing)],[]]) [("X",Just 1),("E",Nothing)]
      (Seq () ((Inp () "X" True) `sSeq` (Inp () "E" False) `sSeq` (Out () "P" False)) (Par ()
        (Pause () "X"
          (Seq () (Fin () (Nop ()) (EmitExt () "P" Nothing) (Nop ())) (Halt ())))
        (Seq () (AwaitInp () "E" Nothing) (Escape () Nothing (Just (Const () 99))))))

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
    it "pause" $
        evalFullProg
            (Seq () ((Inp () "X" True) `sSeq` (Inp () "E" False) `sSeq` (Out () "F" False) `sSeq` (Out () "P" False) `sSeq` (Out () "R" False))
            (Seq ()
                (Pause () "X"
                    (Var' () "x" (Just ((EmitExt () "F" Nothing),(EmitExt () "P" Nothing),(EmitExt () "R" Nothing)))
                        (AwaitInp () "E" Nothing)))
                (Escape () Nothing (Just (Const () 99)))))
            [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
        `shouldBe` Right (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]])

      where
        evalFullProgItRight (res,outss) hist prog =
          (it (printf "pass: %s | %s ~> %d %s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) res (show outss)) $
            (evalFullProg prog hist `shouldBe` Right (res,outss)))

        evalFullProgItLeft err hist prog =
          (it (printf "fail: %s | %s ***%s" (show hist) (G.showProg $ snd $ compile' (True,True) prog) (show err)) $
            (evalFullProg prog hist) `shouldBe` Left err)
