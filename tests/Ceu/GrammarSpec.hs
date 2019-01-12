module Ceu.GrammarSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann      (annz, Ann(..))
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
  describe "checkLoop -- matching-Break/AwaitInp/Every in all paths" $ do

    -- atomic statements --
    checkLoopIt (Loop annz (Write annz (LVar "x") (Call annz "umn" (Const annz 1)))) False
    checkLoopIt (Loop annz (AwaitInp annz "A"))       True
    checkLoopIt (Loop annz (AwaitEvt annz "a"))       False
    checkLoopIt (Loop annz (EmitEvt annz "a"))        False
    checkLoopIt (Loop annz (Escape annz 0))           True
    checkLoopIt (Loop annz (Loop annz (Escape annz 0))) True
    checkLoopIt (Loop annz ((Nop annz)))              False
    checkLoopIt (Loop annz (Error annz ""))           False

    -- compound statements --
    checkLoopIt (Loop annz (Var annz "x" Type0 (Var annz "y" Type0 (Escape annz 0)))) True
    checkLoopIt (Loop annz (Var annz "x" Type0 (Var annz "y" Type0 (Nop annz))))      False

    checkLoopIt (Loop annz (If annz (Const annz 0) (Escape annz 0) (Nop annz)))     False
    checkLoopIt (Loop annz (If annz (Const annz 0) (Fin annz (Nop annz)) (Nop annz))) False
    checkLoopIt (Loop annz (If annz (Const annz 0) (Every annz "A" (Nop annz)) (AwaitInp annz "A"))) True

    checkLoopIt (Loop annz ((Nop annz) `sSeq` (Nop annz) `sSeq` (Escape annz 0) `sSeq` (Nop annz))) True
    checkLoopIt (Loop annz (Trap annz (Loop annz (Escape annz 0)))) False
    checkLoopIt (Loop annz ((Nop annz) `sSeq` (Nop annz) `sSeq` (Loop annz (Escape annz 0)))) True
    checkLoopIt (Loop annz ((Escape annz 0) `sSeq` Loop annz (Nop annz))) True
    checkLoopIt (Loop annz ((Nop annz) `sSeq` Loop annz (Nop annz)))      False

    checkLoopIt (Loop annz (Loop annz (Loop annz (AwaitInp annz "A"))))   True
    checkLoopIt (Loop annz (Loop annz (Escape annz 0)))                 True
    checkLoopIt (Loop annz (Trap annz (Loop annz (Escape annz 0))))       False
    checkLoopIt (Loop annz (Loop annz (Trap annz (Loop annz (Escape annz 0))))) False
    checkLoopIt (Loop annz (Trap annz (Loop annz (Escape annz 0)) `sSeq` (Trap annz (Loop annz (Escape annz 0))))) False
    checkLoopIt (Loop annz (Loop annz (AwaitInp annz "A") `sSeq` Loop annz (Nop annz))) True
    checkLoopIt (Loop annz (Loop annz (Seq annz (Escape annz 0) (Escape annz 0))))  True
    checkLoopIt (Loop annz (Trap annz (Loop annz (Seq annz (Escape annz 0) (Escape annz 0))))) False
    checkLoopIt (Loop annz (Trap annz (Loop annz (Seq annz (Escape annz 0) (Escape annz 1))))) False

    checkLoopIt (Loop annz ((Nop annz) `sPar` (Nop annz) `sPar` (Nop annz))) False
    checkLoopIt (Loop annz (Pause annz "a" (Nop annz)))                    False
    checkLoopIt (Loop annz (Every annz "A" (Nop annz) `sPar` AwaitInp annz "A" `sPar` (Escape annz 0))) True
    checkLoopIt (Loop annz (Pause annz "a" (AwaitInp annz "A")))           True

    -- Fin annz always run in zero time.
    checkLoopIt (Loop annz (Fin annz (Nop annz)))                          False
    checkLoopIt (Loop annz (Fin annz (Escape annz 0)))                     False
    checkLoopIt (Loop annz (Fin annz (AwaitInp annz "A")))                 False
    checkLoopIt (Loop annz (Fin annz (Every annz "A" (Nop annz))))           False

  --------------------------------------------------------------------------
  describe "checkFin/Every -- no Loop/Escape/Await*/Every/Fin:" $ do

    -- atomic statements --
    checkFinIt (Fin annz (Write annz (LVar "x") (Const annz 0))) []
    checkFinIt (Fin annz (AwaitInp annz "A"))        ["invalid statement"]
    checkFinIt (Fin annz (AwaitEvt annz "a"))        ["invalid statement"]
    checkFinIt (Fin annz (EmitEvt annz "a"))         []
    checkFinIt (Fin annz (Escape annz 0))            ["invalid statement"]
    checkFinIt (Fin annz ((Nop annz)))               []
    checkFinIt (Fin annz (Error annz ""))            []

    -- compound statements --
    checkFinIt (Fin annz (Var annz "x" Type0 (Nop annz)))                []
    checkFinIt (Fin annz (Var annz "x" Type0 (Every annz "A" (Nop annz)))) ["invalid statement"]
    checkFinIt (Fin annz (If annz (Const annz 0) (Loop annz (Escape annz 0)) ((Nop annz)))) ["invalid statement"]
    checkFinIt (Fin annz (If annz (Const annz 0) (Write annz (LVar "x") (Const annz 0)) ((Nop annz)))) []
    checkFinIt (Fin annz ((Nop annz) `sSeq` (Nop annz) `sSeq` (AwaitInp annz "A") `sSeq` (Nop annz))) ["invalid statement"]
    checkFinIt (Fin annz ((Nop annz) `sSeq` (Nop annz) `sSeq` (EmitEvt annz "a") `sSeq` (Nop annz)))  []
    checkFinIt (Fin annz (Loop annz (AwaitEvt annz "a")))          ["invalid statement"]
    checkFinIt (Fin annz (Loop annz (AwaitInp annz "A")))          ["invalid statement"]
    checkFinIt (Fin annz ((Nop annz) `sPar` (Nop annz) `sPar` (EmitEvt annz "a"))) ["invalid statement","invalid statement"]

  --------------------------------------------------------------------------
  describe "checkEscape:" $ do

    -- atomic statements --
    checkCheckIt (Error annz "")               []
    checkCheckIt (Escape annz 0)               ["orphan `escape` statement"]
    checkCheckIt (Write annz (LVar "x") (Const annz 0)) ["variable 'x' is not declared"]

    -- compound statements --
    checkCheckIt (Trap annz (Escape annz 0))     []
    checkCheckIt (Trap annz (Escape annz 1))     ["orphan `escape` statement", "missing `escape` statement"]
    checkCheckIt (Trap annz (Trap annz (Escape annz 0))) ["terminating `trap` body","missing `escape` statement"]
    checkCheckIt (Trap annz (Trap annz (Escape annz 1))) ["missing `escape` statement"]
    checkCheckIt (Trap annz (Seq annz (Escape annz 0) (Escape annz 1))) ["orphan `escape` statement","unreachable statement"]
    checkCheckIt (Trap annz (Seq annz (Escape annz 1) (Escape annz 1))) ["orphan `escape` statement","orphan `escape` statement", "missing `escape` statement","unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkReachable:" $ do

    -- atomic statements --
    checkStmtsIt (Error annz "")               []
    checkStmtsIt (Write annz (LVar "x") (Const annz 0)) []

    -- compound statements --
    checkStmtsIt (Seq annz (Escape annz 1) (Escape annz 0)) ["unreachable statement"]
    checkStmtsIt (Seq annz (Trap annz (Trap annz (Escape annz 1))) (Escape annz 0)) ["missing `escape` statement"]
    checkStmtsIt (Seq annz (Escape annz 0) (Escape annz 1)) ["unreachable statement"]
    checkStmtsIt (Seq annz (Halt annz) (Escape annz 1)) ["unreachable statement"]
    checkStmtsIt (Seq annz (Seq annz (Halt annz) (Nop annz)) (Escape annz 1)) ["unreachable statement",("unreachable statement")]
    checkStmtsIt (Seq annz (Loop annz (Nop annz)) (Nop annz)) ["unbounded `loop` execution","unreachable statement"]
    checkStmtsIt (Seq annz (Every annz "" (Nop annz)) (Nop annz)) ["unreachable statement"]
    checkStmtsIt (Seq annz (Par annz (Nop annz) (Every annz "" (Nop annz))) (Nop annz)) ["terminating trail","unreachable statement"]
    checkStmtsIt (Seq annz (Trap annz (Loop annz (Trap annz (Seq annz (Escape annz 0) (Escape annz 1))))) (Nop annz)) ["unreachable statement","unbounded `loop` execution"]
    checkStmtsIt (Seq annz (Trap annz (Loop annz (Trap annz (Seq annz (Escape annz 0) (Nop annz))))) (Nop annz)) ["missing `escape` statement","unreachable statement", "unbounded `loop` execution","unreachable statement"]

  --------------------------------------------------------------------------
  describe "checkTypeSys -- declarations" $ do

    checkTypeSysIt (Nop annz)                                    []
    checkTypeSysIt (Var annz "a" Type0 (Nop annz))                    []
    checkTypeSysIt (Check.prelude annz (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Const annz 1)))) []
    checkTypeSysIt (Check.prelude annz (Var annz "a" (TypeN [Type1 "Int",Type1 "Int"]) (Write annz (LVar "a") (Const annz 1)))) ["types do not match"]
    --checkTypeSysIt (Var annz "a" Type0 (Write annz (LVar "a") (Const annz 1))) ["types do not match"]
    checkTypeSysIt (Var annz "a" Type0 (Write annz (LVar "a") (Const annz 1))) ["types do not match"]
    checkTypeSysIt (Var annz "a" Type0 (If annz (Read annz "a") (Nop annz) (Nop annz))) ["types do not match"]
    checkTypeSysIt (Check.prelude annz (Var annz "a" (Type1 "Int") (If annz (Read annz "a") (Nop annz) (Nop annz)))) ["types do not match"]
    checkTypeSysIt (Data annz "Bool" [] [] False (Var annz "a" (Type1 "Bool") (If annz (Read annz "a") (Nop annz) (Nop annz)))) []
    checkTypeSysIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))    ["variable 'a' is already declared"]
    checkTypeSysIt (Evt annz "e" (Evt annz "e" (Nop annz)))       ["event 'e' is already declared"]
    checkTypeSysIt (Write annz (LVar "a") (Const annz 1))              ["variable 'a' is not declared"]
    checkTypeSysIt (AwaitEvt annz "e")                        ["event 'e' is not declared"]
    checkTypeSysIt (Every annz "e" (Nop annz))                  ["event 'e' is not declared"]
    checkTypeSysIt (Pause annz "a" (Nop annz))                  ["variable 'a' is not declared"]
    checkTypeSysIt (Check.prelude annz (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "umn" (Read annz "b")))))) ["variable 'b' is not declared"]
    checkTypeSysIt (Check.prelude annz (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" Type0 (Write annz (LVar "a") (Call annz "umn" (Read annz "b")))))) ["variable 'b' is not declared","types do not match"]
    checkTypeSysIt (Write annz (LVar "a") (Call annz "f" (Const annz 1))) ["variable 'a' is not declared","function 'f' is not declared"]
    checkTypeSysIt (Var annz "x" (TypeN [Type0,Type0]) (Write annz (LVar "x") (Unit annz)))  ["types do not match"]
    checkTypeSysIt (Check.prelude annz (Var annz "x" (Type1 "Int") (Write annz (LVar "x") (Unit annz)))) ["types do not match"]
    checkTypeSysIt (Check.prelude annz (Func annz "identity" (TypeF (TypeV "a") (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "identity" (Const annz 1)))))) []

    describe "functions" $ do
        it "func ~Int" $
            (fst $ TypeSys.go (Func annz "f" (TypeF Type0 (Type1 "Int")) (Nop annz)))
                `shouldBe` ["type 'Int' is not declared"]

        it "func f; func f" $
            TypeSys.go (Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 Type0) (Nop annz)))
                `shouldBe` ([],Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 Type0) (Nop annz)))

        it "func f[a]; func f[0]" $
            TypeSys.go (Func annz "f" (TypeF (TypeV "a") (TypeV "a")) (Func annz "f" (TypeF Type0 Type0) (Nop annz)))
                `shouldBe` ([],Func annz "f" (TypeF (TypeV "a") (TypeV "a")) (Func annz "f" (TypeF Type0 Type0) (Nop annz)))

        it "func f; func ~f" $
            TypeSys.go (Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 TypeB) (Nop annz)))
                `shouldBe` (["types do not match"],Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 TypeB) (Nop annz)))

        it "input A ; emit A" $
            TypeSys.go (Inp annz "A" (EmitExt annz "A" (Unit annz)))
                `shouldBe` (["output 'A' is not declared"],Inp annz "A" (EmitExt annz "A" (Unit annz{type_=Type0})))

        -- func first :: (a,a)->a ; var a::Int ; a = first((),1)
        checkTypeSysIt (Check.prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Unit annz),(Const annz 1)])))))) ["types do not match"]
        checkTypeSysIt (Check.prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Const annz 1),(Const annz 1)])))))) []

    describe "pattern matching" $ do
        it "_ = 1" $
            TypeSys.go (Write annz LAny (Const annz 1))
            `shouldBe` ([],Write annz{type_=TypeB} LAny (Const annz{type_=Type1 "Int"} 1))
        it "(x,_) = 1" $
            TypeSys.go (Check.prelude annz
                        (Var annz "x" (Type1 "Int")
                            (Write annz (LTuple [LVar "x", LAny]) (Const annz 1))))
            `shouldBe` (["types do not match"],Data annz "Int" [] [] False (Var annz{type_=TypeB} "x" (Type1 "Int") (Write annz{type_=TypeB} (LTuple [LVar "x",LAny]) (Const annz{type_=Type1 "Int"} 1))))
        it "(x,_) = (1,1)" $
            TypeSys.go (Check.prelude annz
                        (Var annz "x" (Type1 "Int")
                            (Write annz (LTuple [LVar "x", LAny]) (Tuple annz [Const annz 1, Const annz 1]))))
            `shouldBe` ([],Data annz "Int" [] [] False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Write (annz{type_ = TypeB}) (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = TypeN [Type1 "Int",Type1 "Int"]}) [Const (annz{type_ = Type1 "Int"}) 1,Const (annz{type_ = Type1 "Int"}) 1]))))
        it "((_,x),_) = (y,1)" $
            TypeSys.go (Check.prelude annz
                        (Var annz "x" (Type1 "Int")
                            (Var annz "y" (TypeN [Type0, Type1 "Int"])
                                (Write annz
                                    (LTuple [LTuple [LAny,LVar "x"], LAny])
                                    (Tuple annz [Read annz "y", Const annz 1])))))
            `shouldBe` ([],Data annz "Int" [] [] False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Var (annz{type_ = TypeB}) "y" (TypeN [Type0,Type1 "Int"]) (Write (annz{type_ = TypeB}) (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = TypeN [TypeN [Type0,Type1 "Int"],Type1 "Int"]}) [Read (annz{type_ = TypeN [Type0,Type1 "Int"]}) "y",Const annz{type_ = Type1 "Int"} 1])))))

  --------------------------------------------------------------------------

  describe "new types" $ do
      describe "bool:" $ do
        it "Bool/Int" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                    (Data annz "Int" [] [] False
                        (Nop annz))))))
            `shouldBe` []

        it "Int/Int" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Int" [] [] False
                    (Data annz "Int" [] [] False
                        (Nop annz))))
            `shouldBe` ["type 'Int' is already declared"]

        it "~Int / x::Int" $
            (fst $ Check.compile (False,False,False)
                (Var annz "x" (Type1 "Int") (Nop annz)))
            `shouldBe` ["type 'Int' is not declared"]

        it "x=Bool" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] True
                    (Var annz "x" (Type1 "Bool")
                        (Write annz (LVar "x") (Cons annz "Bool")))))
            `shouldBe` ["type 'Bool' is abstract"]

        it "Bool ; x=True" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                    (Var annz "x" (Type1 "Bool")
                        (Write annz (LVar "x") (Cons annz "Bool.True")))))))
            `shouldBe` []

        it "Bool ; x=True" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                (Func annz "==" (TypeF (TypeN [(Type1 "Bool"),(Type1 "Bool")]) (Type1 "Bool"))
                    (If annz
                        (Call annz "=="
                            (Tuple annz
                                [Cons annz "Bool.True",
                                 Cons annz "Bool.False"]))
                        (Nop annz)
                        (Nop annz)))))))
            `shouldBe` []

        it "Bool ; x=True" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Int" [] [] True
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                (Func annz "==" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Bool"))
                    (If annz
                        (Call annz "=="
                            (Tuple annz
                                [Cons annz "Bool.True",
                                 Cons annz "Bool.False"]))
                        (Nop annz)
                        (Nop annz))))))))
            `shouldBe` ["types do not match"]

        it "~Bool ; x=True" $
            (fst $ Check.compile (False,False,False)
                (Var annz "x" (Type1 "Bool")
                    (Write annz (LVar "x") (Cons annz{type_=(Type1 "Bool")} "Bool.True"))))
            `shouldBe` ["type 'Bool' is not declared","type 'Bool.True' is not declared"]

      describe "node:" $ do
        it "type Node : Int" $
            (Check.compile (False,False,False)
                (Data annz "Node" [] [DataCons (Right ("Int",[]))] False
                    (Nop annz)))
            `shouldBe` ([],Data annz "Node" [] [DataCons (Right ("Int",[]))] False (Nop annz))

  --------------------------------------------------------------------------

  describe "typeclass" $ do
        it "~Bool ; Equable ; (==)" $
            Check.compile (False,False,False)
                (Class annz "Equalable" ["a"]
                    (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
                        (Nop annz))
                    (Nop annz))
            `shouldBe` (["type 'Bool' is not declared"],(Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

        it "Bool ; Equable ; (==)" $
            Check.compile (False,False,False)
                (Data annz "Bool" [] [] True
                (Class annz "Equalable" ["a"]
                    (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
                    (Nop annz))
                (Nop annz)))
            `shouldBe` ([],Data annz "Bool" [] [] True (Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

        it "Bool ; Equable ; inst ; inst" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["instance 'Equalable (Bool)' is already declared"]

        it "Bool ; Equable a ; inst Equable Bool ; a/=Bool" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Int") (Type1 "Int")) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["TODO: Type0 vs Int"]

        it "Bool ; Equable a ; inst Equable Bool ; a/=Bool" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["TODO: Bool vs Int"]

        it "Bool ; Equable ; (==)" $
            (fst $ Check.compile (False,False,False)
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (CallS annz "fff" (Cons annz "Bool"))))))
            `shouldBe` []

-- TODO: == has to be instantiated as func '== :: (a=Bool,a=Bool)->Bool
        it "Bool ; if True==False ..." $
            (fst $ Check.compile (False,False,False)
                (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                    (If annz
                        (Call annz "=="
                            (Tuple annz
                                [Cons annz "Bool.True",
                                 Cons annz "Bool.False"]))
                        (Nop annz)
                        (Nop annz)))))))
            `shouldBe` []

  --------------------------------------------------------------------------

  describe "checkStmts -- program is valid" $ do

    -- atomic statements --
    checkStmtsIt (Write annz (LVar "c") (Const annz 0)) []
    checkStmtsIt (AwaitInp annz "A")        []
    checkStmtsIt (AwaitEvt annz "a")        []
    checkStmtsIt (EmitEvt annz "a")         []
    checkStmtsIt (Escape annz 0)            []
    checkStmtsIt ((Nop annz))               []
    checkStmtsIt (Error annz "")            []

    -- compound statements --
    checkStmtsIt (Var annz "x" Type0 (Nop annz))              []
    checkStmtsIt (If annz (Const annz 0) (Nop annz) (Escape annz 0)) []
    checkStmtsIt (Seq annz (Escape annz 0) (Nop annz))       ["unreachable statement"]
    checkStmtsIt (Loop annz (Escape annz 0))               ["`loop` never iterates"]
    checkStmtsIt (Loop annz (Nop annz))                    ["unbounded `loop` execution"]
    checkStmtsIt (Every annz "A" (Nop annz))               []
    checkStmtsIt (Every annz "A" (Fin annz (Nop annz)))      ["invalid statement in `every`", "invalid statement"]
    checkStmtsIt (Par annz (Escape annz 0) (Nop annz))       ["terminating trail"]
    checkStmtsIt (Par annz (Escape annz 0) (Halt annz)) []
    checkStmtsIt (Par annz (Halt annz) (Seq annz (EmitEvt annz "a") (Halt annz))) []
    checkStmtsIt (Par annz (Nop annz) (EmitEvt annz "a"))    ["terminating trail"]
    checkStmtsIt (Pause annz "a" (Nop annz))               []
    checkStmtsIt (Fin annz (Nop annz))                     []
    checkStmtsIt (Fin annz (Fin annz (Nop annz)))            ["invalid statement in `finalize`", "invalid statement"]

    -- misc --
    checkStmtsIt ((Nop annz) `sSeq` (Fin annz (Loop annz (Escape annz 0)))) ["`loop` never iterates","invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt ((Nop annz) `sSeq` (Fin annz (Loop annz (Nop annz)))) ["unbounded `loop` execution"]
    checkStmtsIt (Var annz "x" Type0 (Fin annz (Every annz "A" (Nop annz)))) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (Loop annz (Trap annz (Loop annz (Escape annz 0))))   ["`loop` never iterates","unbounded `loop` execution"]
    checkStmtsIt (Loop annz (Trap annz (Loop annz (Seq annz (Escape annz 0) (Escape annz 0))))) ["unreachable statement","`loop` never iterates","unbounded `loop` execution"]
    checkStmtsIt (AwaitEvt annz "a" `sSeq` (Fin annz (Escape annz 0)) `sPar` (Halt annz)) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (AwaitEvt annz "a" `sSeq` (Every annz "A" (Fin annz (Nop annz))) `sPar` (Halt annz)) ["invalid statement in `every`", "invalid statement"]
    checkStmtsIt (Loop annz ((Halt annz) `sPar` Loop annz (Loop annz (Loop annz (AwaitInp annz "A")))))  ["`loop` never iterates","`loop` never iterates","`loop` never iterates"]
    checkStmtsIt (Loop annz ((Escape annz 0) `sPar` Loop annz (Loop annz (Loop annz (AwaitInp annz "A"))))) ["`loop` never iterates","`loop` never iterates","`loop` never iterates"]
    checkStmtsIt (Fin annz (Escape annz 0)) ["invalid statement in `finalize`", "invalid statement"]
    checkStmtsIt (Loop annz (Halt annz)) ["`loop` never iterates"]

    describe "func impl:" $ do
        it "f ... do await end" $
            Check.stmts (FuncI annz "f" TypeB (Loop annz (Nop annz)) (Halt annz))
            `shouldBe` ["unbounded `loop` execution"]
        it "f ... do await end" $
            Check.stmts (FuncI annz "f" TypeB (Halt annz) (Halt annz))
            `shouldBe` ["invalid statement in `func`","invalid statement"]

    -- all
    checkCheckIt (Fin annz (Escape annz 0)) ["orphan `escape` statement", "invalid statement in `finalize`", "invalid statement"]
    checkCheckIt (Trap annz (Fin annz (Escape annz 0))) ["invalid statement in `finalize`", "invalid statement"]
    checkCheckIt (Seq annz (Trap annz (Loop annz (Trap annz (Seq annz (Escape annz 0) (Nop annz))))) (Nop annz)) ["missing `escape` statement", "unreachable statement", "unbounded `loop` execution", "unreachable statement"]
    checkCheckIt (Inp annz "FOREVER" (Trap annz (Seq annz (Trap annz (Par annz (Halt annz) (Escape annz 0))) (Escape annz 0))))
      []
    checkCheckIt (Trap annz (Par annz (Escape annz 0) (Seq annz (Par annz (Inp annz "FOREVER" (Halt annz)) (Fin annz (Nop annz))) (Escape annz 0))))
      ["unreachable statement"]

    describe "ext:" $ do
        it "emit O" $
            (fst $ Check.compile (False,False,False) (EmitExt annz "O" (Unit annz)))
            `shouldBe` ["output 'O' is not declared"]
        it "out O; emit O" $
            Check.compile (False,False,False) (Out annz "O" Type0 (EmitExt annz "O" (Unit annz{type_=Type0})))
            `shouldBe` ([],Out annz "O" Type0 (EmitExt annz "O" (Unit annz{type_=Type0})))
        it "out O::Int; emit O()" $
            Check.compile (False,False,False) (Out annz "O" (Type1 "Int") (EmitExt annz "O" (Unit annz)))
            `shouldBe` (["types do not match"],Out annz "O" (Type1 "Int") (EmitExt annz "O" (Unit annz{type_=Type0})))

        it "await I" $
            (fst $ Check.compile (False,False,False) (AwaitInp annz "I"))
            `shouldBe` ["input 'I' is not declared"]
        it "inp I; await I" $
            Check.compile (False,False,False) (Inp annz "I" (AwaitInp annz "I"))
            `shouldBe` ([], (Inp annz "I" (AwaitInp annz "I")))

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": todo") $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": todo") $
            (ck p) `shouldBe` b)
        checkLoopIt p b      = checkIt  Check.boundedLoop p b
        checkFinIt (Fin _ p) b = checkIt' Check.getComplexs p b
        checkEveryIt p b     = checkIt' Check.getComplexs p b
        checkTypeSysIt p b   = checkIt' (fst.TypeSys.go) p b
        checkStmtsIt p b     = checkIt' Check.stmts p b
        checkCheckIt :: Stmt -> Errors -> Spec
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False,False,False))) p b
