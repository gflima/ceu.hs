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

  describe "declarations" $ do

    checkCheckIt (Write annz (LVar "x") (Const annz 0)) ["variable 'x' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

    checkTypeSysIt (Nop annz)                                    []
    checkTypeSysIt (Var annz "a" Type0 (Nop annz))                    []
    checkTypeSysIt (Check.prelude annz (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Const annz 1)))) []
    checkTypeSysIt (Check.prelude annz (Var annz "a" (TypeN [Type1 "Int",Type1 "Int"]) (Write annz (LVar "a") (Const annz 1)))) ["types do not match : (Int,Int) :> Int"]
    --checkTypeSysIt (Var annz "a" Type0 (Write annz (LVar "a") (Const annz 1))) ["types do not match"]
    checkTypeSysIt (Var annz "a" Type0 (Write annz (LVar "a") (Const annz 1))) ["types do not match : () :> Int"]
    checkTypeSysIt (Var annz "a" Type0 (If annz (Read annz "a") (Nop annz) (Nop annz))) ["types do not match : Bool :> ()"]
    checkTypeSysIt (Check.prelude annz (Var annz "a" (Type1 "Int") (If annz (Read annz "a") (Nop annz) (Nop annz)))) ["types do not match : Bool :> Int"]
    checkTypeSysIt (Data annz "Bool" [] [] False (Var annz "a" (Type1 "Bool") (If annz (Read annz "a") (Nop annz) (Nop annz)))) []
    checkTypeSysIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))    ["variable 'a' is already declared"]
    checkTypeSysIt (Write annz (LVar "a") (Const annz 1))              ["variable 'a' is not declared"]
    checkTypeSysIt (Check.prelude annz (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "umn" (Read annz "b")))))) ["variable 'b' is not declared"]
    checkTypeSysIt (Check.prelude annz (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" Type0 (Write annz (LVar "a") (Call annz "umn" (Read annz "b")))))) ["variable 'b' is not declared","types do not match : () :> Int"]
    checkTypeSysIt (Write annz (LVar "a") (Call annz "f" (Const annz 1))) ["variable 'a' is not declared","function 'f' is not declared"]
    checkTypeSysIt (Var annz "x" (TypeN [Type0,Type0]) (Write annz (LVar "x") (Unit annz)))  ["types do not match : ((),()) :> ()"]
    checkTypeSysIt (Check.prelude annz (Var annz "x" (Type1 "Int") (Write annz (LVar "x") (Unit annz)))) ["types do not match : Int :> ()"]
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
                `shouldBe` (["types do not match : (() -> ()) :> (() -> bot)"],Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 TypeB) (Nop annz)))

        -- func first :: (a,a)->a ; var a::Int ; a = first((),1)
        checkTypeSysIt (Check.prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Unit annz),(Const annz 1)])))))) ["types do not match : (a,a) :> ((),Int)"]
        checkTypeSysIt (Check.prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Const annz 1),(Const annz 1)])))))) []

    describe "pattern matching" $ do
        it "_ = 1" $
            TypeSys.go (Write annz LAny (Const annz 1))
            `shouldBe` ([],Write annz{type_=TypeB} LAny (Const annz{type_=Type1 "Int"} 1))
        it "(x,_) = 1" $
            TypeSys.go (Check.prelude annz
                        (Var annz "x" (Type1 "Int")
                            (Write annz (LTuple [LVar "x", LAny]) (Const annz 1))))
            `shouldBe` (["types do not match : (Int,top) :> Int"],Data annz "Int" [] [] False (Var annz{type_=TypeB} "x" (Type1 "Int") (Write annz{type_=TypeB} (LTuple [LVar "x",LAny]) (Const annz{type_=Type1 "Int"} 1))))
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
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                    (Data annz "Int" [] [] False
                        (Nop annz))))))
            `shouldBe` []

        it "Int/Int" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                    (Data annz "Int" [] [] False
                        (Nop annz))))
            `shouldBe` ["type 'Int' is already declared"]

        it "~Int / x::Int" $
            (fst $ Check.compile (False)
                (Var annz "x" (Type1 "Int") (Nop annz)))
            `shouldBe` ["type 'Int' is not declared"]

        it "x=Bool" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] True
                    (Var annz "x" (Type1 "Bool")
                        (Write annz (LVar "x") (Cons annz "Bool")))))
            `shouldBe` ["type 'Bool' is abstract"]

        it "Bool ; x=True" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] True
                (Data annz "Bool.True" [] [] False
                (Data annz "Bool.False" [] [] False
                    (Var annz "x" (Type1 "Bool")
                        (Write annz (LVar "x") (Cons annz "Bool.True")))))))
            `shouldBe` []

        it "Bool ; x=True" $
            (fst $ Check.compile (False)
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

        it "Int ; Bool.* ; Int==Int ; True==False" $
            (fst $ Check.compile (False)
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
            `shouldBe` ["types do not match : (Int,Int) :> (Bool.True,Bool.False)"]

        it "~Bool ; x=True" $
            (fst $ Check.compile (False)
                (Var annz "x" (Type1 "Bool")
                    (Write annz (LVar "x") (Cons annz{type_=(Type1 "Bool")} "Bool.True"))))
            `shouldBe` ["type 'Bool' is not declared","type 'Bool.True' is not declared"]

      describe "node:" $ do
        it "type Node : Int" $
            (Check.compile (False)
                (Data annz "Node" [] [DataCons (Right ("Int",[]))] False
                    (Nop annz)))
            `shouldBe` ([],Data annz "Node" [] [DataCons (Right ("Int",[]))] False (Nop annz))

  --------------------------------------------------------------------------

  describe "typeclass" $ do
        it "X.f ; X.f" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] False
                (Class annz "X" ["a"] (Nop annz)
                (Class annz "X" ["a"] (Nop annz)
                (Nop annz)))))
            `shouldBe` ["typeclass 'X' is already declared"]

        it "X.f ; Y.f" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] False
                (Class annz "X" ["a"] (Nop annz)
                (Class annz "X" ["a"] (Nop annz)
                (Nop annz)))))
            `shouldBe` ["typeclass 'X' is already declared"]

        it "X.f ; Y.f" $
            (fst $ Check.compile (False)
                (Class annz "X" ["a"]
                    (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
                (Class annz "Y" ["a"]
                    (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
                (Nop annz))))
            `shouldBe` ["function 'f' is already declared"]

        it "X.f ; f" $
            (fst $ Check.compile (False)
                (Class annz "X" ["a"]
                    (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
                (Func annz "f" (TypeF (TypeV "a") Type0)
                (Nop annz))))
            `shouldBe` ["function 'f' is already declared"]

        it "~Bool ; Equalable ; (==)" $
            Check.compile (False)
                (Class annz "Equalable" ["a"]
                    (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
                        (Nop annz))
                    (Nop annz))
            `shouldBe` (["type 'Bool' is not declared"],(Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

        it "Bool ; Equalable ; (==)" $
            Check.compile (False)
                (Data annz "Bool" [] [] True
                (Class annz "Equalable" ["a"]
                    (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
                    (Nop annz))
                (Nop annz)))
            `shouldBe` ([],Data annz "Bool" [] [] True (Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

        it "Bool ; Equalable ; inst ; inst" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["instance 'Equalable (Bool)' is already declared"]

        it "Bool ; Equalable a ; inst Equalable Bool ; ()/=Int" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff1" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff2" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Nop annz)))))
            `shouldBe` ["names do not match : fff1 :> fff2"]

        it "Bool ; Equalable a ; inst Equalable Bool ; ()/=Int" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") (Type1 "Int")) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["types do not match : (a -> ()) :> (Bool -> Int)"]

        it "Bool ; Equalable a ; inst X Bool" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "X" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["typeclass 'X' is not declared","function 'fff' is already declared"]

        it "Bool ; Equalable a ; inst Equalable Bool ; a/=Bool" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
                (Nop annz))))))
            `shouldBe` ["types do not match : Bool :> Int"]

        it "Bool ; Equalable a ; inst Equalable Bool ; fff" $
            (fst $ Check.compile (False)
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (CallS annz "fff" (Cons annz "Bool"))))))
            `shouldBe` []

        it "Int ; Bool ; Equalable a ; inst Equalable Bool ; fff 1" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (CallS annz "fff" (Const annz 1)))))))
            `shouldBe` ["types do not match : Bool :> Int"]

        it "Int ; Bool ; Equalable a ; inst Equalable Bool/Int ; fff 1" $
            (fst $ Check.compile (False)
                (Data annz "Int" [] [] False
                (Data annz "Bool" [] [] False
                (Class annz "Equalable" ["a"]
                    (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
                (Inst annz "Equalable" ["Bool"]
                    (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
                (Inst annz "Equalable" ["Int"]
                    (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
                (CallS annz "fff" (Const annz 1))))))))
            `shouldBe` []

  --------------------------------------------------------------------------

      where
        checkIt ck p b   =
          (it ((if b then "pass" else "fail") ++ ": todo") $
            (ck p) `shouldBe` b)
        checkIt' ck p b   =
          (it ((if b==[] then "pass" else "fail") ++ ": todo") $
            (ck p) `shouldBe` b)
        checkTypeSysIt p b   = checkIt' (fst.TypeSys.go) p b
        checkCheckIt :: Stmt -> Errors -> Spec
        checkCheckIt p b     = checkIt' (fst . (Check.compile (False))) p b
