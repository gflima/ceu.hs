module Ceu.GrammarSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals  (Errors)
import Ceu.Grammar.Ann      (Ann(..))
import Ceu.Grammar.Ann.Unit
import Ceu.Grammar.Type     (Type(..))
import Ceu.Grammar.Exp
import Ceu.Grammar.Stmt
import qualified Ceu.Grammar.Check   as Check
import qualified Ceu.Grammar.TypeSys as TypeSys

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  --------------------------------------------------------------------------
  describe "checkLoop () -- matching-Break/AwaitInp/Every () in all paths" $ do

    -- atomic statements --
    checkLoopIt (Loop () (Write () "x" (Call () "umn" (Const () 1)))) False
    checkLoopIt (Loop () (AwaitInp () "A"))       True
    checkLoopIt (Loop () (AwaitEvt () "a"))       False
    checkLoopIt (Loop () (EmitEvt () "a"))        False
    checkLoopIt (Loop () (Escape () 0))           True
    checkLoopIt (Loop () (Loop () (Escape () 0))) True
    checkLoopIt (Loop () ((Nop ())))              False
    checkLoopIt (Loop () (Error () ""))           False

    -- compound statements --
    checkLoopIt (Loop () (Var () "x" Type0 (Var () "y" Type0 (Escape () 0)))) True
    checkLoopIt (Loop () (Var () "x" Type0 (Var () "y" Type0 (Nop ()))))      False

    checkLoopIt (Loop () (If () (Const () 0) (Escape () 0) (Nop ())))     False
    checkLoopIt (Loop () (If () (Const () 0) (Fin () (Nop ())) (Nop ()))) False
    checkLoopIt (Loop () (If () (Const () 0) (Every () "A" (Nop ())) (AwaitInp () "A"))) True

    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Escape () 0) `sSeq` (Nop ()))) True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0)))) False
    checkLoopIt (Loop () ((Nop ()) `sSeq` (Nop ()) `sSeq` (Loop () (Escape () 0)))) True
    checkLoopIt (Loop () ((Escape () 0) `sSeq` Loop () (Nop ()))) True
    checkLoopIt (Loop () ((Nop ()) `sSeq` Loop () (Nop ())))      False

    checkLoopIt (Loop () (Loop () (Loop () (AwaitInp () "A"))))   True
    checkLoopIt (Loop () (Loop () (Escape () 0)))                 True
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0))))       False
    checkLoopIt (Loop () (Loop () (Trap () (Loop () (Escape () 0))))) False
    checkLoopIt (Loop () (Trap () (Loop () (Escape () 0)) `sSeq` (Trap () (Loop () (Escape () 0))))) False
    checkLoopIt (Loop () (Loop () (AwaitInp () "A") `sSeq` Loop () (Nop ()))) True
    checkLoopIt (Loop () (Loop () (Seq () (Escape () 0) (Escape () 0))))  True
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) False
    checkLoopIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 1))))) False

    checkLoopIt (Loop () ((Nop ()) `sPar` (Nop ()) `sPar` (Nop ()))) False
    checkLoopIt (Loop () (Pause () "a" (Nop ())))                    False
    checkLoopIt (Loop () (Every () "A" (Nop ()) `sPar` AwaitInp () "A" `sPar` (Escape () 0))) True
    checkLoopIt (Loop () (Pause () "a" (AwaitInp () "A")))           True

    -- Fin () always run in zero time.
    checkLoopIt (Loop () (Fin () (Nop ())))                          False
    checkLoopIt (Loop () (Fin () (Escape () 0)))                     False
    checkLoopIt (Loop () (Fin () (AwaitInp () "A")))                 False
    checkLoopIt (Loop () (Fin () (Every () "A" (Nop ()))))           False

  --------------------------------------------------------------------------
  describe "checkFin/Every () -- no Loop/Escape/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin () (Write () "x" (Const () 0))) []
    checkFinIt (Fin () (AwaitInp () "A"))        ["invalid statement"]
    checkFinIt (Fin () (AwaitEvt () "a"))        ["invalid statement"]
    checkFinIt (Fin () (EmitEvt () "a"))         []
    checkFinIt (Fin () (Escape () 0))            ["invalid statement"]
    checkFinIt (Fin () ((Nop ())))               []
    checkFinIt (Fin () (Error () ""))            []

    -- compound statements --
    checkFinIt (Fin () (Var () "x" Type0 (Nop ())))                []
    checkFinIt (Fin () (Var () "x" Type0 (Every () "A" (Nop ())))) ["invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Loop () (Escape () 0)) ((Nop ())))) ["invalid statement"]
    checkFinIt (Fin () (If () (Const () 0) (Write () "x" (Const () 0)) ((Nop ())))) []
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (AwaitInp () "A") `sSeq` (Nop ()))) ["invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sSeq` (Nop ()) `sSeq` (EmitEvt () "a") `sSeq` (Nop ())))  []
    checkFinIt (Fin () (Loop () (AwaitEvt () "a")))          ["invalid statement"]
    checkFinIt (Fin () (Loop () (AwaitInp () "A")))          ["invalid statement"]
    checkFinIt (Fin () ((Nop ()) `sPar` (Nop ()) `sPar` (EmitEvt () "a"))) ["invalid statement","invalid statement"]

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkCheckIt (Error () "")               []
    checkCheckIt (Escape () 0)               ["orphan `escape` statement"]
    checkCheckIt (Write () "x" (Const () 0)) ["identifier 'x' is not declared"]

    -- compound statements --
    checkCheckIt (Trap () (Escape () 0))     []
    checkCheckIt (Trap () (Escape () 1))     ["orphan `escape` statement", "missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 0))) ["terminating `trap` body","missing `escape` statement"]
    checkCheckIt (Trap () (Trap () (Escape () 1))) ["missing `escape` statement"]
    checkCheckIt (Trap () (Seq () (Escape () 0) (Escape () 1))) ["orphan `escape` statement","unreachable statement"]
    checkCheckIt (Trap () (Seq () (Escape () 1) (Escape () 1))) ["orphan `escape` statement","orphan `escape` statement", "missing `escape` statement","unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkStmtsIt (Error () "")               []
    checkStmtsIt (Write () "x" (Const () 0)) []

    -- compound statements --
    checkStmtsIt (Seq () (Escape () 1) (Escape () 0)) ["unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Trap () (Escape () 1))) (Escape () 0)) ["missing `escape` statement"]
    checkStmtsIt (Seq () (Escape () 0) (Escape () 1)) ["unreachable statement"]
    checkStmtsIt (Seq () (Halt ()) (Escape () 1)) ["unreachable statement"]
    checkStmtsIt (Seq () (Seq () (Halt ()) (Nop ())) (Escape () 1)) ["unreachable statement",("unreachable statement")]
    checkStmtsIt (Seq () (Loop () (Nop ())) (Nop ())) ["unbounded `loop` execution","unreachable statement"]
    checkStmtsIt (Seq () (Every () "" (Nop ())) (Nop ())) ["unreachable statement"]
    checkStmtsIt (Seq () (Par () (Nop ()) (Every () "" (Nop ()))) (Nop ())) ["terminating trail","unreachable statement"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Escape () 1))))) (Nop ())) ["unreachable statement","unbounded `loop` execution"]
    checkStmtsIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["missing `escape` statement","unreachable statement", "unbounded `loop` execution","unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkTypeSys -- declarations" $ do

    checkTypeSysIt (Nop ())                                    []
    checkTypeSysIt (Var () "a" Type0 (Nop ()))                    []
    checkTypeSysIt (Var () "a" (Type1 "Int") (Write () "a" (Const () 1))) []
    checkTypeSysIt (Var () "a" (TypeN [Type1 "Int",Type1 "Int"]) (Write () "a" (Const () 1))) ["types do not match"]
    --checkTypeSysIt (Var () "a" Type0 (Write () "a" (Const () 1))) ["types do not match"]
    checkTypeSysIt (Var () "a" Type0 (Write () "a" (Const () 1))) ["types do not match"]
    checkTypeSysIt (Var () "a" Type0 (If () (Read () "a") (Nop ()) (Nop ()))) ["types do not match"]
    checkTypeSysIt (Var () "a" (Type1 "Int") (If () (Read () "a") (Nop ()) (Nop ()))) ["types do not match"]
    checkTypeSysIt (Var () "a" (Type1 "Bool") (If () (Read () "a") (Nop ()) (Nop ()))) []
    checkTypeSysIt (Var () "a" Type0 (Var () "a" Type0 (Nop ())))    ["identifier 'a' is already declared"]
    checkTypeSysIt (Evt () "e" (Evt () "e" (Nop ())))       ["identifier 'e' is already declared"]
    checkTypeSysIt (Write () "a" (Const () 1))              ["identifier 'a' is not declared"]
    checkTypeSysIt (AwaitEvt () "e")                        ["identifier 'e' is not declared"]
    checkTypeSysIt (Every () "e" (Nop ()))                  ["identifier 'e' is not declared"]
    checkTypeSysIt (Pause () "a" (Nop ()))                  ["identifier 'a' is not declared"]
    checkTypeSysIt (Func () "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var () "a" (Type1 "Int") (Write () "a" (Call () "umn" (Read () "b"))))) ["identifier 'b' is not declared"]
    checkTypeSysIt (Func () "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var () "a" Type0 (Write () "a" (Call () "umn" (Read () "b"))))) ["identifier 'b' is not declared","types do not match"]
    checkTypeSysIt (Var () "x" (TypeN [Type0,Type0]) (Write () "x" (Unit ())))  ["types do not match"]
    checkTypeSysIt (Var () "x" (Type1 "Int") (Write () "x" (Unit ()))) ["types do not match"]

  --------------------------------------------------------------------------
  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Write () "c" (Const () 0)) []
    checkStmtsIt (AwaitInp () "A")        []
    checkStmtsIt (AwaitEvt () "a")        []
    checkStmtsIt (EmitEvt () "a")         []
    checkStmtsIt (Escape () 0)            []
    checkStmtsIt ((Nop ()))               []
    checkStmtsIt (Error () "")            []

    -- compound statements --
    checkStmtsIt (Var () "x" Type0 (Nop ()))              []
    checkStmtsIt (If () (Const () 0) (Nop ()) (Escape () 0)) []
    checkStmtsIt (Seq () (Escape () 0) (Nop ()))       ["unreachable statement"]
    checkStmtsIt (Loop () (Escape () 0))               ["`loop` never iterates"]
    checkStmtsIt (Loop () (Nop ()))                    ["unbounded `loop` execution"]
    checkStmtsIt (Every () "A" (Nop ()))               []
    checkStmtsIt (Every () "A" (Fin () (Nop ())))      ["invalid statement in `every`", "invalid statement"]
    checkStmtsIt (Par () (Escape () 0) (Nop ()))       ["terminating trail"]
    checkStmtsIt (Par () (Escape () 0) (Halt ())) []
    checkStmtsIt (Par () (Halt ()) (Seq () (EmitEvt () "a") (Halt ()))) []
    checkStmtsIt (Par () (Nop ()) (EmitEvt () "a"))    ["terminating trail"]
    checkStmtsIt (Pause () "a" (Nop ()))               []
    checkStmtsIt (Fin () (Nop ()))                     []
    checkStmtsIt (Fin () (Fin () (Nop ())))            ["invalid statement in `finalize`", "invalid statement"]

    -- misc --
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Escape () 0)))) ["`loop` never iterates","invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt ((Nop ()) `sSeq` (Fin () (Loop () (Nop ())))) ["unbounded `loop` execution"]
    checkStmtsIt (Var () "x" Type0 (Fin () (Every () "A" (Nop ())))) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (Loop () (Trap () (Loop () (Escape () 0))))   ["`loop` never iterates","unbounded `loop` execution"]
    checkStmtsIt (Loop () (Trap () (Loop () (Seq () (Escape () 0) (Escape () 0))))) ["unreachable statement","`loop` never iterates","unbounded `loop` execution"]
    checkStmtsIt (AwaitEvt () "a" `sSeq` (Fin () (Escape () 0)) `sPar` (Halt ())) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (AwaitEvt () "a" `sSeq` (Every () "A" (Fin () (Nop ()))) `sPar` (Halt ())) ["invalid statement in `every`", "invalid statement"]
    checkStmtsIt (Loop () ((Halt ()) `sPar` Loop () (Loop () (Loop () (AwaitInp () "A")))))  ["`loop` never iterates","`loop` never iterates","`loop` never iterates"]
    checkStmtsIt (Loop () ((Escape () 0) `sPar` Loop () (Loop () (Loop () (AwaitInp () "A"))))) ["`loop` never iterates","`loop` never iterates","`loop` never iterates"]
    checkStmtsIt (Fin () (Escape () 0)) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (Loop () (Halt ())) ["`loop` never iterates"]

    -- all
    checkCheckIt (Fin () (Escape () 0)) ["orphan `escape` statement", "invalid statement in `finalize`", "invalid statement"]
    checkCheckIt (Trap () (Fin () (Escape () 0))) ["invalid statement in `finalize`", "invalid statement"]
    checkCheckIt (Seq () (Trap () (Loop () (Trap () (Seq () (Escape () 0) (Nop ()))))) (Nop ())) ["missing `escape` statement", "unreachable statement", "unbounded `loop` execution", "unreachable statement"]
    checkCheckIt (Inp () "FOREVER" (Trap () (Seq () (Trap () (Par () (Halt ()) (Escape () 0))) (Escape () 0))))
      []
    checkCheckIt (Trap () (Par () (Escape () 0) (Seq () (Par () (Inp () "FOREVER" (Halt ())) (Fin () (Nop ()))) (Escape () 0))))
      ["unreachable statement"]

    describe "ext:" $ do
        it "emit O" $
            (fst $ Check.compile (False,False,False) (EmitExt () "O" Nothing))
            `shouldBe` ["identifier 'O' is not declared"]
        it "out O; emit O" $
            Check.compile (False,False,False) (Out () "O" (EmitExt () "O" Nothing))
            `shouldBe` ([],Out () "O" (EmitExt () "O" Nothing))

        it "await I" $
            (fst $ Check.compile (False,False,False) (AwaitInp () "I"))
            `shouldBe` ["identifier 'I' is not declared"]
        it "inp I; await I" $
            Check.compile (False,False,False) (Inp () "I" (AwaitInp () "I"))
            `shouldBe` ([], (Inp () "I" (AwaitInp () "I")))

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": " ++ show p) $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": " ++ show p) $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt  Check.boundedLoop p b
        checkFinIt (Fin () p) b = checkIt' Check.getComplexs (traceShowId p) b
        checkEveryIt p b     = checkIt' Check.getComplexs p b
        checkTypeSysIt p b   = checkIt' (fst.TypeSys.go) p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt :: Stmt () -> Errors -> Spec
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False,False))) p b
