module Ceu.BasicSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann    (annz, Ann(..))
import Ceu.Grammar.Type   (Type(..))
import Ceu.Grammar.Basic
import qualified Ceu.Grammar.TypeSys as TypeSys

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "declarations" $ do

  checkCheckIt (Write annz (LVar "x") (Number annz 0)) ["variable 'x' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

  checkCheckIt (Nop annz)                  []
  checkCheckIt (Var annz "a" Type0 (Nop annz))          []
  checkCheckIt (prelude annz (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Number annz 1)))) []
  checkCheckIt (prelude annz (Var annz "a" (TypeN [Type1 "Int",Type1 "Int"]) (Write annz (LVar "a") (Number annz 1)))) ["types do not match : expected '(Int,Int)' : found 'Int'"]
  --checkCheckIt (Var annz "a" Type0 (Write annz (LVar "a") (Number annz 1))) ["types do not match"]
  checkCheckIt (Var annz "a" Type0 (Write annz (LVar "a") (Number annz 1))) ["types do not match : expected '()' : found 'Int'"]
  checkCheckIt (Var annz "a" Type0 (If annz (Read annz "a") (Nop annz) (Nop annz))) ["types do not match : expected 'Bool' : found '()'"]
  checkCheckIt (prelude annz (Var annz "a" (Type1 "Int") (If annz (Read annz "a") (Nop annz) (Nop annz)))) ["types do not match : expected 'Bool' : found 'Int'"]
  checkCheckIt (Data annz "Bool" [] [] False (Var annz "a" (Type1 "Bool") (If annz (Read annz "a") (Nop annz) (Nop annz)))) []
  checkCheckIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))  ["variable 'a' is already declared"]
  checkCheckIt (Write annz (LVar "a") (Number annz 1))        ["variable 'a' is not declared"]

  checkCheckIt (prelude annz (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "umn" (Read annz "b"))))))
               ["variable 'b' is not declared"]

  checkCheckIt (prelude annz
                (Func annz "umn" (TypeF (Type1 "Int") (Type1 "Int"))
                (Var annz "a" Type0
                (Write annz (LVar "a") (Call annz "umn" (Read annz "b"))))))
               ["types do not match : expected '(Int -> Int)' : found '(_ -> ())'", "variable 'b' is not declared","types do not match : expected '()' : found 'Int'"]

  checkCheckIt (Write annz (LVar "a") (Call annz "f" (Number annz 1))) ["variable 'a' is not declared","function 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0]) (Write annz (LVar "x") (Unit annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (Type1 "Int") (Write annz (LVar "x") (Unit annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Func annz "identity" (TypeF (TypeV "a") (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "identity" (Number annz 1)))))) []

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
      TypeSys.go (Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 TypeT) (Nop annz)))
        `shouldBe` (["types do not match : expected '(() -> ())' : found '(() -> top)'"],Func annz "f" (TypeF Type0 Type0) (Func annz "f" (TypeF Type0 TypeT) (Nop annz)))

    -- func first :: (a,a)->a ; var a::Int ; a = first((),1)
    checkCheckIt (prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Unit annz),(Number annz 1)]))))))
                 ["types do not match : expected '((a,a) -> a)' : found '(((),Int) -> Int)'","ambigous instances for 'a' : '()', 'Int', 'Int'"]

    checkCheckIt (prelude annz (Func annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz "first" (Tuple annz [(Number annz 1),(Number annz 1)])))))) []

  describe "pattern matching" $ do
    it "_ = 1" $
      TypeSys.go (Write annz LAny (Number annz 1))
      `shouldBe` ([],Write annz{type_=TypeB} LAny (Number annz{type_=Type1 "Int"} 1))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Write annz (LTuple [LVar "x", LAny]) (Number annz 1))))
      `shouldBe` (["types do not match : expected '(Int,top)' : found 'Int'"],Data annz "Int" [] [] False (Var annz{type_=TypeB} "x" (Type1 "Int") (Write annz{type_=TypeB} (LTuple [LVar "x",LAny]) (Number annz{type_=Type1 "Int"} 1))))
    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Write annz (LTuple [LVar "x", LAny]) (Tuple annz [Number annz 1, Number annz 1]))))
      `shouldBe` ([],Data annz "Int" [] [] False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Write (annz{type_ = TypeB}) (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = TypeN [Type1 "Int",Type1 "Int"]}) [Number (annz{type_ = Type1 "Int"}) 1,Number (annz{type_ = Type1 "Int"}) 1]))))
    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Var annz "y" (TypeN [Type0, Type1 "Int"])
                (Write annz
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Number annz 1])))))
      `shouldBe` ([],Data annz "Int" [] [] False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Var (annz{type_ = TypeB}) "y" (TypeN [Type0,Type1 "Int"]) (Write (annz{type_ = TypeB}) (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = TypeN [TypeN [Type0,Type1 "Int"],Type1 "Int"]}) [Read (annz{type_ = TypeN [Type0,Type1 "Int"]}) "y",Number annz{type_ = Type1 "Int"} 1])))))

  --------------------------------------------------------------------------

  describe "new types" $ do
    describe "bool:" $ do
    it "Bool/Int" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] [] True
        (Data annz "Bool.True" [] [] False
        (Data annz "Bool.False" [] [] False
          (Data annz "Int" [] [] False
            (Nop annz))))))
      `shouldBe` []

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
          (Data annz "Int" [] [] False
            (Nop annz))))
      `shouldBe` ["type 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 "Int") (Nop annz)))
      `shouldBe` ["type 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] [] True
          (Var annz "x" (Type1 "Bool")
            (Write annz (LVar "x") (Cons annz "Bool")))))
      `shouldBe` ["type 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] [] True
        (Data annz "Bool.True" [] [] False
        (Data annz "Bool.False" [] [] False
          (Var annz "x" (Type1 "Bool")
            (Write annz (LVar "x") (Cons annz "Bool.True")))))))
      `shouldBe` []

    it "Bool ; x=True" $
      (fst $ TypeSys.go
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
      (fst $ TypeSys.go
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
      `shouldBe` ["types do not match : expected '((Int,Int) -> Bool)' : found '((Bool.True,Bool.False) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 "Bool")
          (Write annz (LVar "x") (Cons annz{type_=(Type1 "Bool")} "Bool.True"))))
      `shouldBe` ["type 'Bool' is not declared","type 'Bool.True' is not declared"]

    describe "node:" $ do
    it "type Node : Int" $
      (TypeSys.go
        (Data annz "Node" [] [DataCons (Right ("Int",[]))] False
          (Nop annz)))
      `shouldBe` ([],Data annz "Node" [] [DataCons (Right ("Int",[]))] False (Nop annz))

  --------------------------------------------------------------------------

  describe "typeclass" $ do
    it "X.f ; X.f" $
      (fst $ TypeSys.go
        (Class annz "X" ["a"] (Nop annz)
        (Class annz "X" ["a"] (Nop annz)
        (Nop annz))))
      `shouldBe` ["typeclass 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst $ TypeSys.go
        (Class annz "X" ["a"]
          (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Class annz "Y" ["a"]
          (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Nop annz))))
      `shouldBe` ["function 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz "X" ["a"]
          (Func annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Func annz "f" (TypeF (TypeV "a") Type0)
        (Nop annz))))
      `shouldBe` ["function 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz "Equalable" ["a"]
          (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
            (Nop annz))
          (Nop annz))
      `shouldBe` (["type 'Bool' is not declared"],(Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz "Bool" [] [] True
        (Class annz "Equalable" ["a"]
          (Func annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
          (Nop annz))
        (Nop annz)))
      `shouldBe` ([],Data annz "Bool" [] [] True (Class annz "Equalable" ["a"] (Func annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff1" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff2" (TypeF (Type1 "A") Type0) (Nop annz))
        (Nop annz)))))
      `shouldBe` ["names do not match : expected 'fff1' : found 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") (Type1 "Int")) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "X" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["typeclass 'X' is not declared","function 'fff' is already declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (CallS annz "fff" (Cons annz "A"))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [TypeN [Type1 "A", Type1 "A"]]
          (Func annz "fff" (TypeF (TypeN [Type1 "A", Type1 "A"]) Type0) (Nop annz))
        (CallS annz "fff" (Tuple annz [(Cons annz "A"),(Cons annz "A")])))))
      `shouldBe` ([],Data annz "A" [] [] False (Class annz "Xable" ["a"] (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [TypeN [Type1 "A",Type1 "A"]] (Func annz "fff" (TypeF (TypeN [Type1 "A",Type1 "A"]) Type0) (Nop annz)) (SCallS annz "(A,A)__fff" (Tuple annz{type_=TypeN [Type1 "A",Type1 "A"]} [Cons annz{type_=Type1 "A"} "A",Cons annz{type_=Type1 "A"} "A"])))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "A" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (CallS annz "fff" (Number annz 1)))))))
      `shouldBe` ["call for 'fff' has no instance in 'Xable'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "Bool" [] [] False
        (Class annz "Equalable" ["a"]
          (Func annz "eq" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool")) (Nop annz))
        (CallS annz "eq" (Tuple annz [(Cons annz "Bool"),(Number annz 1)]))))))
      `shouldBe` ["types do not match : expected '((a,a) -> Bool)' : found '((Bool,Int) -> _)'",
                  "ambigous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (TypeSys.go
        (Data annz "Int" [] [] False
        (Data annz "Bool" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "Bool"]
          (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "Int"]
          (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz))
        (Seq annz
          (CallS annz "fff" (Number annz 1))
          (CallS annz "fff" (Cons annz "Bool")))))))))
      `shouldBe` ([],Data annz "Int" [] [] False (Data annz "Bool" [] [] False (Class annz "Xable" ["a"] (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "Bool"] (Func annz "fff" (TypeF (Type1 "Bool") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "Int"] (Func annz "fff" (TypeF (Type1 "Int") Type0) (Nop annz)) (Seq annz (SCallS annz "Int__fff" (Number annz{type_=Type1 "Int"} 1)) (SCallS annz "Bool__fff" (Cons annz{type_=Type1 "Bool"} "Bool"))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (TypeSys.go
        (Data annz "A" [] [] False
        (Data annz "A.B" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (CallS annz "fff" (Cons annz "A.B")))))))
      `shouldBe` ([],Data annz "A" [] [] False (Data annz "A.B" [] [] False (Class annz "Xable" ["a"] (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "A"] (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz)) (SCallS annz "A__fff" (Cons annz{type_=Type1 "A.B"} "A.B"))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (TypeSys.go
        (Data annz "A" [] [] False
        (Data annz "A.B" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A.B"]
          (Func annz "fff" (TypeF (Type1 "A.B") Type0) (Nop annz))
        (CallS annz "fff" (Cons annz "A.B"))))))))
      `shouldBe` ([],Data annz "A" [] [] False (Data annz "A.B" [] [] False (Class annz "Xable" ["a"] (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "A"] (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "A.B"] (Func annz "fff" (TypeF (Type1 "A.B") Type0) (Nop annz)) (SCallS annz "A.B__fff" (Cons annz{type_=Type1 "A.B"} "A.B")))))))

    it "A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz "A" [] [] False
        (Data annz "A.B" [] [] False
        (Class annz "Xable" ["a"]
          (Func annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A.B"]
          (Func annz "fff" (TypeF (Type1 "A.B") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Func annz "fff" (TypeF (Type1 "A") Type0) (Nop annz))
        (CallS annz "fff" (Cons annz "A.B"))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

    describe "return-type polymorphism" $ do

      it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
        (TypeSys.go
          (Data annz "B" [] [] False
          (Class annz "X" ["b"]
            (Func annz "fff" (TypeF Type0 (TypeV "b")) (Nop annz))
          (Inst annz "X" [Type1 "B"]
            (Func annz "fff" (TypeF Type0 (Type1 "B")) (Nop annz))
          (CallS annz "fff" (Unit annz))))))
        `shouldBe` ([],Data annz "B" [] [] False (Class annz "X" ["b"] (Func annz "fff" (TypeF Type0 (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B"] (Func annz "fff" (TypeF Type0 (Type1 "B")) (Nop annz)) (SCallS annz "B__fff" (Unit annz{type_=Type0})))))

      it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
        (TypeSys.go
          (Data annz "B" [] [] False
          (Class annz "X" ["b"]
            (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
          (Inst annz "X" [Type1 "B"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B")) (Nop annz))
          (CallS annz "fff" (Unit annz))))))
        `shouldBe` ([],Data annz "B" [] [] False (Class annz "X" ["b"] (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B")) (Nop annz)) (SCallS annz "B__fff" (Unit annz{type_=Type0})))))

      it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
        (TypeSys.go
          (Data annz "B1" [] [] False
          (Data annz "B2" [] [] False
          (Class annz "X" ["b"]
            (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
          (Inst annz "X" [Type1 "B1"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz))
          (Inst annz "X" [Type1 "B2"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz))
          (CallS annz "fff" (Unit annz))))))))
        `shouldBe` (["TODO: should be error because both B1/B2 are ok"],
                    -- the problem is that CallS accept any return type
                    Data annz "B1" [] [] False (Data annz "B2" [] [] False (Class annz "X" ["b"] (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz)) (Inst annz "X" [Type1 "B2"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz)) (SCallS annz "B[12]__fff" (Unit annz{type_=Type0})))))))

      it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
        (TypeSys.go
          (Data annz "B1" [] [] False
          (Data annz "B2" [] [] False
          (Class annz "X" ["b"]
            (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
          (Inst annz "X" [Type1 "B1"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz))
          (Inst annz "X" [Type1 "B2"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz))
          (Var annz "b1" (Type1 "B1")
          (Write annz (LVar "b1")
            (Call annz "fff" (Unit annz))))))))))
        `shouldBe` ([],Data annz "B1" [] [] False (Data annz "B2" [] [] False (Class annz "X" ["b"] (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz)) (Inst annz "X" [Type1 "B2"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz)) (Var annz "b1" (Type1 "B1") (Write annz (LVar "b1") (SCall annz{type_=Type1 "B1"} "B1__fff" (Unit annz{type_=Type0})))))))))

      it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
        (TypeSys.go
          (Data annz "B1" [] [] False
          (Data annz "B2" [] [] False
          (Class annz "X" ["b"]
            (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
          (Inst annz "X" [Type1 "B1"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz))
          (Inst annz "X" [Type1 "B2"]
            (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz))
          (Var annz "b2" (Type1 "B2")
          (Write annz (LVar "b2")
            (Call annz "fff" (Unit annz))))))))))
        `shouldBe` ([],Data annz "B1" [] [] False (Data annz "B2" [] [] False (Class annz "X" ["b"] (Func annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Nop annz)) (Inst annz "X" [Type1 "B2"] (Func annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Nop annz)) (Var annz "b2" (Type1 "B2") (Write annz (LVar "b2") (SCall annz{type_=Type1 "B2"} "B2__fff" (Unit annz{type_=Type0})))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
