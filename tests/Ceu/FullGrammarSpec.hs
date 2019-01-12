module Ceu.FullGrammarSpec (main, spec) where

import Ceu.Grammar.Globals (Loc(..))
import Ceu.Grammar.Type (Type(..))
import Ceu.Grammar.Ann (Ann(type_),annz)
import Ceu.Grammar.Exp
import qualified Ceu.Grammar.Stmt as G
import qualified Ceu.Eval         as E
import Ceu.Grammar.Full.Stmt
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
instance NFData Stmt where
  rnf (Nop _) = ()
  rnf (Seq _ p q) = rnf p `seq` rnf q

-- Force full evaluation of a given NFData.
forceEval :: NFData a => a -> IO a
forceEval = evaluate . force

defs = (Seq annz
        (Func annz "==" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Bool")))
        (Seq annz
            (Func annz "+" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
            (Seq annz
                (Func annz "-" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int")))
                (Func annz "*" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Int"))))))

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --describe "TODO" $ do
  --------------------------------------------------------------------------
  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        Scope.compile (Var annz "x" Type0 Nothing)
        `shouldBe` ([], (Var' annz "x" Type0 Nothing (Nop annz)))

      it "var x; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" Type0 Nothing) (Nop annz))
        `shouldBe` ([], (Var' annz "x" Type0 Nothing (Nop annz)))

      it "var x <- 1 ; (Nop annz)" $ do
        Scope.compile (Seq annz (Var annz "x" (Type1 "Int") Nothing) (Seq annz (Write annz (LVar "x") (Const annz 1)) (Nop annz)))
        `shouldBe` ([], (Var' annz "x" (Type1 "Int") Nothing (Seq annz (Write annz (LVar "x") (Const annz 1)) (Nop annz))))

      it "scope var x end ; var y" $ do
        Scope.compile (Seq annz (Scope annz (Var annz "x" Type0 Nothing)) (Var annz "y" Type0 Nothing))
        `shouldBe` ([],Seq annz (Var' annz "x" Type0 Nothing (Nop annz)) (Var' annz "y" Type0 Nothing (Nop annz)))

      it "scope var x end ; x=1" $ do
        compile' (False,False,False) (Seq annz (Scope annz (Var annz "x" (Type1 "Int") Nothing)) (Write annz (LVar "x") (Const annz 1)))
        `shouldBe` (["type 'Int' is not declared","variable 'x' is not declared"], G.Seq annz (G.Var annz "x" (Type1 "Int") (G.Nop annz)) (G.Write annz (LVar "x") (Const (annz{type_=Type1 "Int"}) 1)))

      it "var x" $ do
        compile' (False,True,False) (Var annz "x" Type0 Nothing)
        `shouldBe` (["terminating `trap` body","missing `escape` statement","unreachable statement","type 'Int' is not declared"], G.Inp annz "TIMER" (G.Var annz "_ret" (Type1 "Int") (G.Seq annz (G.Trap annz (G.Var annz "x" Type0 (G.Nop annz))) (G.Halt annz))))

      it "var x" $ do
        compile' (True,True,False) (Var annz "x" Type0 Nothing)
        `shouldBe` (["terminating `trap` body","missing `escape` statement","unreachable statement","type 'Int' is not declared"], G.Inp annz "TIMER" (G.Var annz "_ret" (Type1 "Int") (G.Halt annz)))

    describe "int:" $ do
      it "int x" $ do
        Scope.compile (Evt annz "x" Type0)
        `shouldBe` ([], (Evt' annz "x" Type0 (Nop annz)))

      it "int x; (Nop annz)" $ do
        Scope.compile (Seq annz (Evt annz "x" Type0) (Nop annz))
        `shouldBe` ([], (Evt' annz "x" Type0 (Nop annz)))

      it "scope int x end ; int y" $ do
        Scope.compile (Seq annz (Scope annz (Evt annz "x" Type0)) (Evt annz "y" Type0))
        `shouldBe` ([],Seq annz (Evt' annz "x" Type0 (Nop annz)) (Evt' annz "y" Type0 (Nop annz)))

      it "scope int x end ; x=1" $ do
        compile' (False,False,False) (Seq annz (Scope annz (Evt annz "x" Type0)) (EmitEvt annz "x" Nothing))
        `shouldBe` (["event 'x' is not declared"], G.Seq annz (G.Evt annz "x" (G.Nop annz)) (G.EmitEvt annz "x"))

    describe "output:" $ do
      it "output X" $ do
        Scope.compile (Out annz "X" Type0)
        `shouldBe` ([], (Out' annz "X" Type0 (Nop annz)))

      it "output X; (Nop annz)" $ do
        Scope.compile (Seq annz (Out annz "X" Type0) (Nop annz))
        `shouldBe` ([], (Out' annz "X" Type0 (Nop annz)))

      it "scope ext X end ; ext y" $ do
        Scope.compile (Seq annz (Scope annz (Out annz "X" Type0)) (Out annz "Y" Type0))
        `shouldBe` ([],Seq annz (Out' annz "X" Type0 (Nop annz)) (Out' annz "Y" Type0 (Nop annz)))

      it "scope ext X end ; X=1" $ do
        compile' (False,False,False) (Seq annz (Scope annz (Out annz "X" Type0)) (EmitEvt annz "X" Nothing))
        `shouldBe` (["event 'X' is not declared"], G.Seq annz (G.Out annz "X" Type0 (G.Nop annz)) (G.EmitEvt annz "X"))

      it "scope escape 1 end" $ do
        compile' (False,False,False) (Scope annz (Escape annz Nothing (Const annz 1)))
        `shouldBe` (["orphan `escape` statement"],G.Escape annz (-1))

      it "scope escape 1 end" $ do
        compile' (False,True,False) (Scope annz (Escape annz Nothing (Const annz 1)))
        `shouldBe` (["type 'Int' is not declared"],G.Inp annz "TIMER" (G.Var annz "_ret" (Type1 "Int") (G.Seq annz (G.Trap annz (G.Seq annz (G.Write annz (LVar "_ret") (Const annz{type_=Type1 "Int"} 1)) (G.Escape annz 0))) (G.Halt annz))))

  --------------------------------------------------------------------------
  describe "Trap.compile" $ do

    it "trap escape;" $ do
      Trap.compile (Trap annz Nothing (Escape annz Nothing (Unit annz)))
      `shouldBe` ([], (Trap' annz (Escape' annz 0)))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' annz "a" Type0 Nothing (Trap annz (Just "a") (Escape annz (Just "a") (Unit annz))))
      `shouldBe` ([], (Var' annz "a" Type0 Nothing (Trap' annz (Seq annz (Write annz (LVar "a") (Unit annz)) (Escape' annz 0)))))

    it "trap/a escape/a;" $ do
      Trap.compile (Var' annz "ret" Type0 Nothing (Trap annz (Just "ret") (Escape annz (Just "ret") (Const annz 1))))
      `shouldBe` ([], (Var' annz "ret" Type0 Nothing (Trap' annz (Seq annz (Write annz (LVar "ret") (Const annz 1)) (Escape' annz 0)))))

    it "trap/a trap escape/a;" $ do
      Trap.compile (Var' annz "ret" Type0 Nothing (Trap annz (Just "ret") (Trap annz Nothing (Escape annz (Just "ret") (Unit annz)))))
      `shouldBe` ([],Var' annz "ret" Type0 Nothing (Trap' annz (Trap' annz (Seq annz (Write annz (LVar "ret") (Unit annz)) (Escape' annz 1)))))

    it "trap/a escape;" $ do
      Trap.compile (Var' annz "ret" Type0 Nothing (Trap annz (Just "ret") (Escape annz Nothing (Unit annz))))
      `shouldBe` ([], (Var' annz "ret" Type0 Nothing (Trap' annz (Seq annz (Write annz (LVar "ret") (Unit annz)) (Escape' annz 0)))))

    it "trap/a escape/b;" $ do
      Trap.compile (Var' annz "ret" Type0 Nothing (Trap annz (Just "ret") (Escape annz (Just "xxx") (Const annz 1))))
      `shouldBe` ([], (Var' annz "ret" Type0 Nothing (Trap' annz (Escape' annz (-1)))))

    it "trap/a escape/a;" $ do
      compile' (False,False,False) (Var' annz "ret" Type0 Nothing (Trap annz (Just "ret") (Escape annz (Just "xxx") (Const annz 1))))
      `shouldBe` (["orphan `escape` statement","missing `escape` statement"], (G.Var annz "ret" Type0 (G.Trap annz (G.Escape annz (-1)))))

  --------------------------------------------------------------------------
  describe "Fin.compile" $ do
    it "fin ..." $ do
      Fin.compile (Fin annz (Nop annz) (Nop annz) (Nop annz))
      `shouldBe` (["unexpected `finalize`"],Or' annz (Nop annz) (Par annz (Halt annz) (Fin' annz (Nop annz))))

    it "fin fin nop" $ do
      Fin.compile (Fin annz (Fin annz (Nop annz) (Nop annz) (Nop annz)) (Nop annz) (Nop annz))
      `shouldBe` (["unexpected `finalize`","unexpected `finalize`"],Or' annz (Nop annz) (Par annz (Halt annz) (Fin' annz (Or' annz (Nop annz) (Par annz (Halt annz) (Fin' annz (Nop annz)))))))

    it "var x; fin x with nop; nop" $ do
      Fin.compile (Var' annz "x" Type0 (Just ((Nop annz),(Nop annz),(Nop annz))) (Nop annz))
      `shouldBe` ([], (Var' annz "x" Type0 Nothing (Or' annz (Nop annz) (Par annz (Halt annz) (Fin' annz (Nop annz))))))

    it "var x; { fin x with nop; nop }" $ do
      Fin.compile (Var' annz "x" Type0 (Just ((Nop annz),(Nop annz),(Nop annz))) (Var' annz "y" Type0 Nothing (Nop annz)))
      `shouldBe` ([], (Var' annz "x" Type0 Nothing (Or' annz (Var' annz "y" Type0 Nothing (Nop annz)) (Par annz (Halt annz) (Fin' annz (Nop annz))))))

    it "var x; { fin x with x=1; fin with x=2; x=3 }" $ do
      Fin.compile (Var' annz "x" Type0 (Just ((Write annz (LVar "x") (Const annz 1)),(Nop annz),(Nop annz))) (Var' annz "y" Type0 Nothing (Seq annz (Fin annz (Write annz (LVar "x") (Const annz 2)) (Nop annz) (Nop annz)) (Write annz (LVar "x") (Const annz 3)))))
      `shouldBe` ([], (Var' annz "x" Type0 Nothing (Or' annz (Var' annz "y" Type0 Nothing (Or' annz (Write annz (LVar "x") (Const annz 3)) (Par annz (Halt annz) (Fin' annz (Write annz (LVar "x") (Const annz 2)))))) (Par annz (Halt annz) (Fin' annz (Write annz (LVar "x") (Const annz 1)))))))

    it "var x; { fin x with x=1; fin x with y=1; y=3 }" $ do
      Fin.compile (Var' annz "x" Type0 (Just (((Write annz (LVar "x") (Const annz 1)) `sSeq` (Write annz (LVar "y") (Const annz 1))),(Nop annz),(Nop annz))) (Var' annz "_" Type0 Nothing (Write annz (LVar "y") (Const annz 3))))
      `shouldBe` ([], (Var' annz "x" Type0 Nothing (Or' annz (Var' annz "_" Type0 Nothing (Write annz (LVar "y") (Const annz 3))) (Par annz (Halt annz) (Fin' annz (Seq annz (Write annz (LVar "x") (Const annz 1)) (Write annz (LVar "y") (Const annz 1))))))))

    it "var x; nop; { fin x with x=1; fin with x=2; x=3; fin x with y=1; fin with y=2; y=3 }; nop" $ do
      Fin.compile
        (Var' annz "x" Type0 (Just ((Write annz (LVar "x") (Const annz 1) `sSeq` (Write annz (LVar "y") (Const annz 1)) `sSeq` (Nop annz)),(Nop annz),(Nop annz)))
                 (Seq annz (Nop annz)
                   (Seq annz
                     (Var' annz "_" Type0 Nothing (
                       (Fin annz (Write annz (LVar "x") (Const annz 2)) (Nop annz) (Nop annz)) `sSeq`
                       (Write annz (LVar "x") (Const annz 3))               `sSeq`
                       (Fin annz (Write annz (LVar "y") (Const annz 2)) (Nop annz) (Nop annz)) `sSeq`
                       (Write annz (LVar "y") (Const annz 3))))
                     (Nop annz))))
      `shouldBe`
        ([], (Var' annz "x" Type0 Nothing
                 (Or' annz
                   (Seq annz
                     (Nop annz)
                     (Seq annz
                       (Var' annz "_" Type0 Nothing
                         (Or' annz
                           (Seq annz
                             (Write annz (LVar "x") (Const annz 3))
                             (Or' annz
                               (Write annz (LVar "y") (Const annz 3))
                               (Par annz (Halt annz) (Fin' annz (Write annz (LVar "y") (Const annz 2))))))
                           (Par annz (Halt annz) (Fin' annz (Write annz (LVar "x") (Const annz 2))))))
                       (Nop annz)))
                    (Par annz (Halt annz) (Fin' annz (Seq annz (Write annz (LVar "x") (Const annz 1)) (Seq annz (Write annz (LVar "y") (Const annz 1)) (Nop annz))))))))

  --------------------------------------------------------------------------
  describe "Async.compile" $ do

    it "async { loop nop }" $ do
      Async.compile (Async annz (Loop annz (Nop annz)))
      `shouldBe` ([], (Loop annz (Seq annz (Nop annz) (AwaitInp annz "ASYNC" Nothing))))

  --------------------------------------------------------------------------
  describe "Spawn.compile" $ do

    it "spawn nop;" $ do
      Spawn.compile (Spawn annz (Nop annz))
      `shouldBe` (["unexpected `spawn`"],Or' annz (Clean' annz "Spawn" (Nop annz)) (Nop annz))

    it "nop; spawn nop;" $ do
      Spawn.compile (Seq annz (Nop annz) (Spawn annz (Nop annz)))
      `shouldBe` (["unexpected `spawn`"],Seq annz (Nop annz) (Or' annz (Clean' annz "Spawn" (Nop annz)) (Nop annz)))

    it "spawn nop; nop" $ do
      Spawn.compile (Seq annz (Spawn annz (Nop annz)) (Nop annz))
      `shouldBe` ([], Or' annz (Clean' annz "Spawn" (Nop annz)) (Nop annz))

    it "spawn nop; nop" $ do
      compile' (False,False,False) (Seq annz (Spawn annz (Nop annz)) (Nop annz))
      `shouldBe` (["terminating `spawn`"], G.Trap annz (G.Par annz (G.Seq annz (G.Nop annz) (G.Halt annz)) (G.Seq annz (G.Nop annz) (G.Escape annz 0))))

    it "spawn awaitFor; nop" $ do
      Spawn.compile (Seq annz (Spawn annz (Halt annz)) (Nop annz))
      `shouldBe` ([], Or' annz (Clean' annz "Spawn" (Halt annz)) (Nop annz))

    it "spawn escape || escape" $ do
      compile' (False,False,False) (Trap annz (Just "a") (Seq annz (Spawn annz (Par annz (Escape annz Nothing (Const annz 1)) (Escape annz (Just "a") (Unit annz)))) (Nop annz)))
      `shouldBe` (["escaping `spawn`","escaping statement","escaping statement","terminating `trap` body","variable 'a' is not declared","variable 'a' is not declared"],G.Trap annz (G.Trap annz (G.Par annz (G.Par annz (G.Seq annz (G.Write annz (LVar "a") (Const annz{type_=Type1 "Int"} 1)) (G.Escape annz 1)) (G.Seq annz (G.Write annz (LVar "a") (Unit annz{type_=Type0})) (G.Escape annz 1))) (G.Seq annz (G.Nop annz) (G.Escape annz 0)))))

  --------------------------------------------------------------------------
  describe "ParAndOr.compile" $ do
    it "(and nop nop)" $ do
      ParAndOr.compile (Seq annz defs (And annz (Nop annz) (Nop annz))) `shouldBe` ([], (Seq annz (Seq annz (Func annz "==" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Bool"))) (Seq annz (Func annz "+" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int"))) (Seq annz (Func annz "-" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int"))) (Func annz "*" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int")))))) (Clean' annz "And" (Trap' annz (Var' annz "__and" (Type1 "Int") Nothing (Seq annz (Write annz (LVar "__and") (Const annz 0)) (Par' annz (Seq annz (Nop annz) (If annz (Call annz "==" (Tuple annz [(Read annz "__and"),(Const annz 1)])) (Escape' annz 0) (Seq annz (Write annz (LVar "__and") (Call annz "+" (Tuple annz [(Read annz "__and"),(Const annz 1)]))) (Halt annz)))) (Seq annz (Nop annz) (If annz (Call annz "==" (Tuple annz [(Read annz "__and"),(Const annz 1)])) (Escape' annz 0) (Seq annz (Write annz (LVar "__and") (Call annz "+" (Tuple annz [(Read annz "__and"),(Const annz 1)]))) (Halt annz)))))))))))
    it "(or nop awaitFor)" $ do
      ParAndOr.compile (Or annz (Nop annz) (Halt annz)) `shouldBe` ([], (Clean' annz "Or" (Trap' annz (Par' annz (Seq annz (Nop annz) (Escape' annz 0)) (Seq annz (Halt annz) (Escape' annz 0))))))
    it "(or nop awaitFor)" $ do
      (compile' (False,False,False) (Or annz (Nop annz) (Halt annz))) `shouldBe` ([], (G.Trap annz (G.Par annz (G.Seq annz (G.Nop annz) (G.Escape annz 0)) (G.Halt annz))))
    it "(and nop (and nop nop))" $ do
      (compile' (False,False,False) (And annz (Nop annz) (And annz (Nop annz) (Nop annz)))) `shouldBe` ([], G.Seq annz (G.Nop annz) (G.Seq annz (G.Nop annz) (G.Nop annz)))
    it "par for par for par for" $ do
      (compile' (True,False,False) (Par annz (Halt annz) (Par annz (Halt annz) (Halt annz))))
      `shouldBe` ([], G.Halt annz)
    it "or nop or nop or for" $ do
      (compile' (True,False,False) (Or annz (Nop annz) (Or annz (Nop annz) (Halt annz))))
      `shouldBe` ([], G.Nop annz)
    it "and nop and nop and nop" $ do
      (compile' (True,False,False) (And annz (Nop annz) (And annz (Nop annz) (Nop annz))))
      `shouldBe` ([], G.Nop annz)
    it "(loop break) ; await X and nop" $ do
      (fst $ compile' (True,True,False) (Seq annz (Data annz "Bool" [] [] False) (Seq annz (Data annz "Int" [] [] False) (Seq annz defs (And annz (Seq annz (Loop annz (Break annz)) (Seq annz (Inp annz "X" Type0) (AwaitInp annz "X" Nothing))) (Nop annz))))))
      `shouldBe` ["terminating `trap` body","missing `escape` statement","`loop` never iterates","unreachable statement","type 'Int' is not declared"]
    it "(loop break) ; await X and nop" $ do
      (fst $ compile' (False,True,False) (Seq annz (Data annz "Bool" [] [] False) (Seq annz (Data annz "Int" [] [] False) (Seq annz defs (Seq annz (And annz (Seq annz (Loop annz (Break annz)) (AwaitInp annz "X" Nothing)) (Nop annz)) (Escape annz Nothing (Const annz 1)) )))))
      `shouldBe` ["`loop` never iterates","type 'Int' is not declared","input 'X' is not declared"]

  --------------------------------------------------------------------------
  describe "(Break annz).compile" $ do

    it "loop (or break FOR)" $ do
      compile (Loop annz (Or annz (Break annz) (Halt annz)))
      `shouldBe` ([], Clean' annz "Loop" (Trap' annz (Loop annz (Clean' annz "Or" (Trap' annz (Par' annz (Seq annz (Escape' annz 1) (Escape' annz 0)) (Seq annz (Halt annz) (Escape' annz 0))))))))

    it "loop (or break FOR)" $ do
      compile' (False,False,False) (Loop annz (Or annz (Break annz) (Halt annz)))
      `shouldBe` (["no trails terminate","`loop` never iterates"], (G.Trap annz (G.Loop annz (G.Par annz (G.Escape annz 0) (G.Halt annz)))))

    it "loop (par break FOR)" $ do
      compile' (False,False,False) (Loop annz (Par annz (Break annz) (Halt annz)))
      `shouldBe` (["`loop` never iterates"], (G.Trap annz (G.Loop annz (G.Par annz (G.Escape annz 0) (G.Halt annz)))))

    it "loop (and break FOR)" $ do
      compile' (False,False,False) (Loop annz (And annz (Break annz) (Halt annz)))
      `shouldBe` (["trail must terminate","trail must terminate","unreachable statement","`loop` never iterates"],G.Trap annz (G.Loop annz (G.Seq annz (G.Escape annz 0) (G.Halt annz))))

  --------------------------------------------------------------------------
{-
  describe "Forever.compile" $ do

    it "await FOREVER;" $ do
      Forever.compile (Halt annz)
      `shouldBe` ([], (Halt annz))
-}

  --------------------------------------------------------------------------
  describe "compile'" $ do

    it "var x;" $ do
      compile' (False,False,False) (Var' annz "x" Type0 Nothing (Nop annz))
      `shouldBe` ([], (G.Var annz "x" Type0 (G.Nop annz)))
    it "var x;" $ do
      compile' (True,False,False) (Var' annz "x" Type0 Nothing (Nop annz))
      `shouldBe` ([], ((G.Nop annz)))

    it "do var x; x = 1 end" $ do
      compile' (False,False,False) (Var' annz "x" (Type1 "Int") Nothing (Write annz (LVar "x") (Const annz 1)))
      `shouldBe` (["type 'Int' is not declared"], (G.Var annz "x" (Type1 "Int") (G.Write annz (LVar "x") (Const annz{type_=Type1 "Int"} 1))))

    it "spawn do await A; end ;; await B; var x; await FOREVER;" $ do
      compile' (False,False,False) (Seq annz (Inp annz "A" Type0) (Seq annz (Inp annz "B" Type0) (Seq annz (Spawn annz (AwaitInp annz "A" Nothing)) (Seq annz (AwaitInp annz "B" Nothing) (Var' annz "x" Type0 Nothing (Halt annz))))))
      `shouldBe` (["terminating `spawn`"], G.Inp annz "A" (G.Inp annz "B" (G.Par annz (G.Seq annz (G.AwaitInp annz "A") (G.Halt annz)) (G.Seq annz (G.AwaitInp annz "B") (G.Var annz "x" Type0 (G.Halt annz))))))

    it "spawn do async ret++ end ;; await F;" $ do
      compile' (False,False,False) (Seq annz (Data annz "Bool" [] [] False) (Seq annz (Data annz "Int" [] [] False) (Seq annz defs (Seq annz (Inp annz "ASYNC" Type0) (Seq annz (Inp annz "A" Type0) (Seq annz (Spawn annz (Async annz (Loop annz (Write annz (LVar "x") (Call annz "+" (Tuple annz [(Read annz "x"),(Const annz 1)])))))) (AwaitInp annz "A" Nothing)))))))
      `shouldBe` (["variable 'x' is not declared","variable 'x' is not declared"], G.Data annz "Bool" [] [] False (G.Data annz "Int" [] [] False (G.Func annz "==" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Bool")) (G.Func annz "+" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int")) (G.Func annz "-" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int")) (G.Func annz "*" (TypeF (TypeN [Type1 "Int",Type1 "Int"]) (Type1 "Int")) (G.Inp annz "ASYNC" (G.Inp annz "A" (G.Trap annz (G.Par annz (G.Loop annz (G.Seq annz (G.Write annz (LVar "x") (Call annz{type_=Type1 "Int"} "+" (Tuple annz{type_=(TypeN [TypeT,Type1 "Int"])} [(Read annz{type_=TypeT} "x"),(Const annz{type_=Type1 "Int"} 1)]))) (G.AwaitInp annz "ASYNC"))) (G.Seq annz (G.AwaitInp annz "A") (G.Escape annz 0))))))))))))

    it "trap terminates" $ do
      compile' (False,False,False) (Or annz (Trap' annz (Escape' annz 0)) (Halt annz))
      `shouldBe` ([], (G.Trap annz (G.Par annz (G.Seq annz (G.Trap annz (G.Escape annz 0)) (G.Escape annz 0)) (G.Halt annz))))

    it "removes unused trap" $ do
      compile' (False,False,False) (Seq annz (Fin annz (Nop annz) (Nop annz) (Nop annz)) (Halt annz))
      `shouldBe` ([], G.Par annz (G.Halt annz) (G.Par annz (G.Halt annz) (G.Fin annz (G.Nop annz))))

    it "nested or/or/fin" $ do
      compile' (False,False,False)
        (Or annz
          (Halt annz)
          (Or annz
            (Seq annz (Fin annz (Nop annz) (Nop annz) (Nop annz)) (Halt annz))
            (Nop annz)))
      `shouldBe`
        ([], G.Trap annz
          (G.Par annz
            (G.Halt annz)
            (G.Seq annz
              (G.Trap annz
                (G.Par annz
                  (G.Par annz
                    (G.Halt annz)
                    (G.Par annz (G.Halt annz) (G.Fin annz (G.Nop annz))))
                  (G.Seq annz (G.Nop annz) (G.Escape annz 0))))
              (G.Escape annz 0))))

  --------------------------------------------------------------------------
  describe "misc" $ do
    it "error \"Hello!\"" $ do
      evaluate $ evalFullProg (Error annz "Hello!") []
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
      (Escape annz Nothing (Const annz 25))

    -- TODO: OK
    evalFullProgItRight (10,[[]]) [] (
      (Var' annz "a" (Type1 "Int") (Just ((Nop annz),(Nop annz),(Nop annz)))
        (Escape annz Nothing (Const annz 10))
      ))

    -- TODO: OK
    evalFullProgItLeft ["variable 'b' is not declared"] [] (
      (Var' annz "ret" (Type1 "Int") Nothing (
      (Var' annz "a" (Type1 "Int") (Just ((Write annz (LVar "ret") (Read annz "b")),(Nop annz),(Nop annz)))
        (Var' annz "b" (Type1 "Int") Nothing
          (Seq annz
            (Write annz (LVar "b") (Const annz 99))
            (Escape annz Nothing (Const annz 0))
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
      (Evt' annz "a" Type0 (
      (Var' annz "ret" (Type1 "Int") Nothing (
      (Write annz (LVar "ret") (Const annz 0)) `sSeq`
      (Par annz
        ((AwaitEvt annz "a" Nothing) `sSeq` (Escape annz Nothing (Call annz "+" (Tuple annz [(Read annz "ret"),(Const annz 5)]))))
        (Seq annz
          (Or annz
            (
              (Fin annz (
                (Write annz (LVar "ret") (Call annz "*" (Tuple annz [(Read annz "ret"),(Const annz 2)]))) `sSeq`
                (EmitEvt annz "a" Nothing)
              ) (Nop annz) (Nop annz)) `sSeq`
              (Halt annz)
            )
            (Write annz (LVar "ret") (Call annz "+" (Tuple annz [(Read annz "ret"),(Const annz 10)])))
          )
          (Halt annz))
      ))))))

    evalFullProgItLeft ["no trails terminate"] []
      (Or annz
        (Loop annz (AwaitTmr annz (Const annz 5)))
        (Escape annz Nothing (Const annz 25)))

    evalFullProgItLeft ["trail must terminate","trail must terminate","terminating `trap` body","unreachable statement","unreachable statement"] []
      (And annz
        (Loop annz (AwaitTmr annz (Const annz 5)))
        (Escape annz Nothing (Const annz 25)))

    evalFullProgItRight (25,[[]]) []
      (Par annz
        (Loop annz (AwaitTmr annz (Const annz 5)))
        (Escape annz Nothing (Const annz 25)))

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
      Evt' annz "a" (Type1 "Int") (
        Par annz
          (Var' annz "ret" (Type1 "Int") Nothing (Seq annz (AwaitEvt annz "a" (Just $ LVar "ret")) (Escape annz Nothing (Read annz "ret"))))
          (EmitEvt annz "a" (Just (Const annz 10)) `sSeq` (Halt annz))
      ))

    evalFullProgItLeft ["variable '_a' is not declared","variable '_a' is not declared"] []
      (Var' annz "ret" (Type1 "Int") Nothing
        (Evt' annz "a" Type0 (
          Par annz
            (Seq annz (AwaitEvt annz "a" (Just $ LVar "ret")) (Escape annz Nothing (Const annz 0)))
            (EmitEvt annz "a" (Just (Const annz 10)) `sSeq` (Halt annz)))))

    evalFullProgItLeft ["variable '_a' is not declared"] [] (
      (Evt' annz "a" Type0
        (Seq annz
          (And annz
            (AwaitEvt annz "a" Nothing)
            (EmitEvt annz "a" (Just (Const annz 10))))
          (Escape annz Nothing (Const annz 0)))))

    evalFullProgItRight (99,[[]]) [] (
      (Evt' annz "a" Type0 (
        Par annz
          ((AwaitEvt annz "a" Nothing) `sSeq` (Escape annz Nothing (Const annz 99)))
          (EmitEvt annz "a" Nothing `sSeq` (Halt annz))
      )))
    evalFullProgItRight (99,[[]]) [] (
      (Evt' annz "a" (Type1 "Int") (
        Par annz
          ((AwaitEvt annz "a" Nothing) `sSeq` (Escape annz Nothing (Const annz 99)))
          (EmitEvt annz "a" (Just (Const annz 10)) `sSeq` (Halt annz))
      )))
    evalFullProgItLeft ["varsRead: uninitialized variable: _a"] []
      (Var' annz "ret" (Type1 "Int") Nothing
        (Evt' annz "a" Type0 (
          Par annz
            (Seq annz (AwaitEvt annz "a" (Just $ LVar "ret")) (Escape annz Nothing (Read annz "ret")))
            (EmitEvt annz "a" Nothing `sSeq` (Halt annz)))))

{-
par/or do
    every A in ret do end
with
    await F;
end
-}
    -- TODO: OK
    evalFullProgItLeft ["varsRead: uninitialized variable: _A"] [("A",Nothing)]
      (Seq annz (Inp annz "F" Type0)
      (Seq annz (Inp annz "A" Type0)
      (Var' annz "ret" (Type1 "Int") Nothing
        (Seq annz
          (Or annz
            (Every annz "A" (Just $ LVar "ret") (Nop annz))
            (AwaitInp annz "F" Nothing))
          (Escape annz Nothing (Read annz "ret"))))))

    evalFullProgItRight (99,[[],[],[],[]]) [("A",Just 1),("A",Just 99),("F",Just 2)]
      (Seq annz (Inp annz "A" (Type1 "Int"))
      (Seq annz (Inp annz "F" (Type1 "Int"))
      (Var' annz "ret" (Type1 "Int") Nothing
        (Par annz
          (Every annz "A" (Just $ LVar "ret") (Nop annz))
          (Seq annz (AwaitInp annz "F" Nothing) (Escape annz Nothing (Read annz "ret")))))))

  describe "timers" $ do

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq annz (AwaitTmr annz (Const annz 10)) (Escape annz Nothing (Const annz 10)))
    evalFullProgItLeft ["pending inputs"] [("TIMER",Just 11)]
      (Seq annz (AwaitTmr annz (Const annz 10)) (Escape annz Nothing (Const annz 10)))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5)) `sSeq` (Escape annz Nothing (Const annz 10)))
    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      ((AwaitTmr annz (Const annz 8)) `sSeq` (AwaitTmr annz (Const annz 2)) `sSeq` (Escape annz Nothing (Const annz 10)))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq annz
        (And annz
          (AwaitTmr annz (Const annz 10))
          (AwaitTmr annz (Const annz 10)))
        (Escape annz Nothing (Const annz 10)))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 10)]
      (Seq annz
        (And annz
          ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5)))
          ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5))))
        (Escape annz Nothing (Const annz 10)))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq annz
        (And annz
          ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5)))
          ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5))))
        (Seq annz
          (AwaitTmr annz (Const annz 10))
          (Escape annz Nothing (Const annz 10))))

    evalFullProgItRight (10,[[],[]]) [("TIMER",Just 20)]
      (Seq annz
        (And annz
          ((AwaitTmr annz (Const annz 5)) `sSeq` (AwaitTmr annz (Const annz 5)))
          ((AwaitTmr annz (Const annz 4)) `sSeq` (AwaitTmr annz (Const annz 5))))
        (Seq annz
          (AwaitTmr annz (Const annz 10))
          (Escape annz Nothing (Const annz 10))))

    evalFullProgItLeft ["output 'A' is not declared"] []
      (Seq annz (Inp annz "A" Type0) (Seq annz (EmitExt annz "A" (Unit annz)) (Escape annz Nothing (Const annz 1))))

    evalFullProgItRight
      (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])
      [("TIMER",Just 10),("TIMER",Just 11)]
      (Seq annz (Out annz "A" (Type1 "Int")) (Seq annz (Out annz "B" (Type1 "Int")) (Seq annz (Out annz "C" (Type1 "Int")) (Seq annz
        (And annz
          ((AwaitTmr annz (Const annz 5)) `sSeq` (EmitExt annz "A" (Const annz 1)) `sSeq` (AwaitTmr annz (Const annz 5)) `sSeq` (EmitExt annz "A" (Const annz 2)))
          ((AwaitTmr annz (Const annz 4)) `sSeq` (EmitExt annz "B" (Const annz 1)) `sSeq` (AwaitTmr annz (Const annz 7) `sSeq` (EmitExt annz "B" (Const annz 2)))))
        (
          (AwaitTmr annz (Const annz 10))          `sSeq`
          (EmitExt annz "C" (Const annz 1)) `sSeq`
          (Escape annz Nothing (Const annz 10)))))))

    it "xxx" $
        evalFullProg
            (Seq annz
                ((Out annz "A" (Type1 "Int")) `sSeq` (Out annz "B" (Type1 "Int")) `sSeq` (Out annz "C" (Type1 "Int")))
                (Seq annz
                    (And annz
                        ((AwaitTmr annz (Const annz 5))             `sSeq`
                        (EmitExt annz "A" (Const annz 1))           `sSeq`
                        (AwaitTmr annz (Const annz 5))              `sSeq`
                        (EmitExt annz "A" (Const annz 2)))

                        ((AwaitTmr annz (Const annz 4))             `sSeq`
                        (EmitExt annz "B" (Const annz 1))           `sSeq`
                        (AwaitTmr annz (Const annz 7)               `sSeq`
                        (EmitExt annz "B" (Const annz 2)))))
                    (
                        (AwaitTmr annz (Const annz 10))          `sSeq`
                        (EmitExt annz "C" (Const annz 1))        `sSeq`
                        (Escape annz Nothing (Const annz 10)))))
            [("TIMER",Just 10),("TIMER",Just 11)]
        `shouldBe` Right (10,[[],[("B",Just 1),("A",Just 1),("A",Just 2)],[("B",Just 2),("C",Just 1)]])

  describe "outputs" $ do

    evalFullProgItRight (1,[[],[("O",Just 1)],[("O",Just 2)],[]]) [("I",Just 1),("I",Just 2),("F",Nothing)]
      (Seq annz ((Inp annz "I" (Type1 "Int")) `sSeq` (Inp annz "F" Type0) `sSeq` (Out annz "O" (Type1 "Int"))) (Var' annz "i" (Type1 "Int") Nothing
        (Par annz
          (Seq annz (AwaitInp annz "F" Nothing) (Escape annz Nothing (Const annz 1)))
          (Every annz "I" (Just $ LVar "i") (EmitExt annz "O" (Read annz "i"))))))

  describe "pause" $ do

    evalFullProgItRight (99,[[]]) []
      (Evt' annz "x" (Type1 "Int") (Pause annz "x" (Escape annz Nothing (Const annz 99))))

    evalFullProgItRight (99,[[]]) []
      (Seq annz ((Inp annz "X" (Type1 "Int")) `sSeq` (Inp annz "A" Type0)) (Par annz
        (Seq annz (AwaitInp annz "X" Nothing) (Escape annz Nothing (Const annz 33)))
        (Evt' annz "x" (Type1 "Int")
          (Pause annz "x"
            (Seq annz
              (EmitEvt annz "x" (Just (Const annz 1)))
              (Escape annz Nothing (Const annz 99)))))))

    evalFullProgItRight (99,[[],[],[],[],[]]) [("X",(Just 1)),("A",Nothing),("X",(Just 0)),("A",Nothing)]
      (Seq annz ((Inp annz "X" (Type1 "Int")) `sSeq` (Inp annz "A" Type0)) (Seq annz
        (Pause annz "X" (AwaitInp annz "A" Nothing))
        (Escape annz Nothing (Const annz 99))))

    evalFullProgItRight (99,[[],[("P",Nothing)],[]]) [("X",Just 1),("E",Nothing)]
      (Seq annz ((Inp annz "X" (Type1 "Int")) `sSeq` (Inp annz "E" Type0) `sSeq` (Out annz "P" Type0)) (Par annz
        (Pause annz "X"
          (Seq annz (Fin annz (Nop annz) (EmitExt annz "P" (Unit annz)) (Nop annz)) (Halt annz)))
        (Seq annz (AwaitInp annz "E" Nothing) (Escape annz Nothing (Const annz 99)))))

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
            (Seq annz ((Inp annz "X" (Type1 "Int")) `sSeq` (Inp annz "E" Type0) `sSeq` (Out annz "F" Type0) `sSeq` (Out annz "P" Type0) `sSeq` (Out annz "R" Type0))
            (Seq annz
                (Pause annz "X"
                    (Var' annz "x" Type0 (Just ((EmitExt annz "F" (Unit annz)),(EmitExt annz "P" (Unit annz)),(EmitExt annz "R" (Unit annz))))
                        (AwaitInp annz "E" Nothing)))
                (Escape annz Nothing (Const annz 99))))
            [("X",Just 1),("E",Nothing),("X",Just 0),("E",Nothing)]
        `shouldBe` Right (99,[[],[("P",Nothing)],[],[("R",Nothing)],[("F",Nothing)]])

  describe "func:" $ do
      it "call f" $ do
          (compile' (False,True,False)
              (Seq annz (Seq annz
                (Func annz "f" (TypeF (Type1 "Int") (Type1 "Int")))
                (FuncI annz "f"
                    (TypeF (Type1 "Int") (Type1 "Int"))
                    (Escape annz Nothing (Const annz 1))))
                (Escape annz Nothing (Call annz "f" (Const annz 1)))))
          `shouldBe` (["type 'Int' is not declared","type 'Int' is not declared","type 'Int' is not declared","type 'Int' is not declared"],
                (G.Inp annz "TIMER"
                    (G.Var annz "_ret" (Type1 "Int")
                        (G.Seq annz
                            (G.Trap annz
                                (G.Func annz "f" (TypeF (Type1 "Int") (Type1 "Int"))
                                    (G.FuncI annz "f" (TypeF (Type1 "Int") (Type1 "Int"))
                                        (G.Var annz "_fret" (Type1 "Int")
                                            (G.Trap annz
                                                (G.Seq annz
                                                    (G.Write annz (LVar "_fret") (Const (annz {type_ = Type1 "Int"}) 1))
                                                    (G.Escape annz 0))))
                                    (G.Seq annz
                                        (G.Write annz (LVar "_ret") (Call (annz {type_ = Type1 "Int"}) "f" (Const (annz {type_ = Type1 "Int"}) 1)))
                                        (G.Escape annz 0)))))
                            (G.Halt annz)))))

      where
        evalFullProgItRight (res,outss) hist prog =
          (it "todo" $
            (evalFullProg prog hist `shouldBe` Right (res,outss)))

        evalFullProgItLeft err hist prog =
          (it "todo" $
            (evalFullProg prog hist) `shouldBe` Left err)
