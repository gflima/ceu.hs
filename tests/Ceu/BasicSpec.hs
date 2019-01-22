module Ceu.BasicSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann    (annz, Ann(..))
import Ceu.Grammar.Type   (Type(..))
import Ceu.Grammar.Basic
import qualified Ceu.Grammar.Simplify as Simplify
import qualified Ceu.Grammar.TypeSys  as TypeSys

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
  checkCheckIt (Data annz "Bool" [] Type0 False (Var annz "a" (Type1 "Bool") (If annz (Read annz "a") (Nop annz) (Nop annz)))) []
  checkCheckIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))  ["variable 'a' is already declared"]
  checkCheckIt (Write annz (LVar "a") (Number annz 1))        ["variable 'a' is not declared"]

  checkCheckIt (prelude annz (Var annz "umn" (TypeF (Type1 "Int") (Type1 "Int")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz (Read annz "umn") (Read annz "b"))))))
               ["variable 'b' is not declared"]

  checkCheckIt
    (prelude annz
      (Var annz "umn" (TypeF (Type1 "Int") (Type1 "Int"))
      (Var annz "a" Type0
      (Write annz (LVar "a") (Call annz (Read annz "umn") (Read annz "b"))))))
    ["variable 'b' is not declared"]

  checkCheckIt
    (prelude annz
      (Var annz "umn" (TypeF (Type1 "Int") (Type1 "Int"))
      (Var annz "a" Type0
      (Write annz (LVar "a") (Call annz (Read annz "umn") (Number annz 1))))))
    ["types do not match : expected '(Int -> ())' : found '(Int -> Int)'"]

  checkCheckIt (Write annz (LVar "a") (Call annz (Read annz "f") (Number annz 1))) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0]) (Write annz (LVar "x") (Unit annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (Type1 "Int") (Write annz (LVar "x") (Unit annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TypeF (TypeV "a") (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz (Read annz "identity") (Number annz 1)))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Var annz "ret" TypeT
        (Write annz (LVar "ret") (Number annz 1)))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Var annz "a" TypeT
        (Var annz "b" TypeT
        (Write annz (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2]))))))
        `shouldBe` []
    it "ret = f()" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Var annz "f" (TypeF Type0 (Type1 "Int"))
        (Var annz "ret" TypeT
        (Write annz (LVar "ret") (Call annz (Read annz "f") (Unit annz)))))))
        `shouldBe` []

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TypeF Type0 (Type1 "Int")) (Nop annz)))
        `shouldBe` ["type 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (Var annz "f" (TypeF (TypeV "a") (TypeV "a")) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF (TypeV "a") (TypeV "a")) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))

    it "func f; func ~f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 TypeT) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 TypeT) (Nop annz)))

    -- func first :: (a,a)->a ; var a::Int ; a = first((),1)
    checkCheckIt
      (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Unit annz),(Number annz 1)]))))))
      ["types do not match : expected '(a,a)' : found '((),Int)'","ambigous instances for 'a' : '()', 'Int'"]

    checkCheckIt (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 "Int") (Write annz (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Number annz 1),(Number annz 1)])))))) []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 Type0)
        (Write annz (LVar "f")
          (Func annz (TypeF Type0 Type0)
            (Ret annz (Arg annz))))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 (TypeV "a"))
        (Ret annz (Call annz (Read annz "f") (Unit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Var annz "f" (TypeF (TypeV "a") (Type1 "Int"))
        (Ret annz (Call annz (Read annz "f") (Number annz 1))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz "Int" [] Type0 False
        (Class annz "X" ["a"]
            (Var annz "fff" (TypeF (TypeV "a") (Type1 "Int")) (Nop annz))
        (Inst annz "X" [Type1 "Int"]
            (Var annz "fff" (TypeF (Type1 "Int") (Type1 "Int"))
            (Seq annz
            (Write annz
              (LVar "fff")
              (Func annz (TypeF (Type1 "Int") (Type1 "Int"))
                (Ret annz (Number annz 1))))
            (Nop annz)))
        (Ret annz (Call annz (Read annz "fff") (Number annz 1)))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "2 = 1" $
      TypeSys.go (Write annz (LNumber 1) (Number annz 1))
      `shouldBe` ([],Write annz{type_=TypeB} (LNumber 1) (Number annz{type_=Type1 "Int"} 1))
    it "_ = 1" $
      TypeSys.go (Write annz LAny (Number annz 1))
      `shouldBe` ([],Write annz{type_=TypeB} LAny (Number annz{type_=Type1 "Int"} 1))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Write annz (LTuple [LVar "x", LAny]) (Number annz 1))))
      `shouldBe` (["types do not match : expected '(Int,top)' : found 'Int'"],Data annz "Int" [] Type0 False (Var annz{type_=TypeB} "x" (Type1 "Int") (Write annz{type_=TypeB} (LTuple [LVar "x",LAny]) (Number annz{type_=Type1 "Int"} 1))))
    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Write annz (LTuple [LVar "x", LAny]) (Tuple annz [Number annz 1, Number annz 1]))))
      `shouldBe` ([],Data annz "Int" [] Type0 False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Write (annz{type_ = TypeB}) (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = TypeN [Type1 "Int",Type1 "Int"]}) [Number (annz{type_ = Type1 "Int"}) 1,Number (annz{type_ = Type1 "Int"}) 1]))))
    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 "Int")
              (Var annz "y" (TypeN [Type0, Type1 "Int"])
                (Write annz
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Number annz 1])))))
      `shouldBe` ([],Data annz "Int" [] Type0 False (Var (annz{type_ = TypeB}) "x" (Type1 "Int") (Var (annz{type_ = TypeB}) "y" (TypeN [Type0,Type1 "Int"]) (Write (annz{type_ = TypeB}) (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = TypeN [TypeN [Type0,Type1 "Int"],Type1 "Int"]}) [Read (annz{type_ = TypeN [Type0,Type1 "Int"]}) "y",Number annz{type_ = Type1 "Int"} 1])))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (Type1 "Int") (Write annz (LRead "a") (Number annz 1))))
      `shouldBe` ([],Data annz "Int" [] Type0 False (Var annz "a" (Type1 "Int") (Write annz (LRead "a") (Number annz{type_=Type1 "Int"} 1))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" Type0 (Write annz (LRead "a") (Number annz 1))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],Data annz "Int" [] Type0 False (Var annz "a" Type0 (Write annz (LRead "a") (Number annz{type_=Type1 "Int"} 1))))

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] Type0 True
        (Data annz "Bool.True" [] Type0 False
        (Data annz "Bool.False" [] Type0 False
        (Data annz "Int" [] Type0 False
        (Nop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz "Bool.True" [] Type0 False
        (Data annz "Bool" [] Type0 True
        (Data annz "Bool.False" [] Type0 False
        (Nop annz)))))
      `shouldBe` ["type 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz "Bool.True.Xxx" [] Type0 False (Nop annz)))
      `shouldBe` ["type 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "Int" [] Type0 False
        (Nop annz))))
      `shouldBe` ["type 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 "Int") (Nop annz)))
      `shouldBe` ["type 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] Type0 True
          (Var annz "x" (Type1 "Bool")
            (Write annz (LVar "x") (Cons annz "Bool" (Unit annz))))))
      `shouldBe` ["type 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] Type0 True
        (Data annz "Bool.True" [] Type0 False
        (Data annz "Bool.False" [] Type0 False
          (Var annz "x" (Type1 "Bool")
            (Write annz (LVar "x") (Cons annz "Bool.True" (Unit annz))))))))
      `shouldBe` []

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz "Bool" [] Type0 True
        (Data annz "Bool.True" [] Type0 False
        (Data annz "Bool.False" [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 "Bool"),(Type1 "Bool")]) (Type1 "Bool"))
          (If annz
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz "Bool.True" (Unit annz),
                 Cons annz "Bool.False" (Unit annz)]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "Int ; Bool.* ; Int==Int ; True==False" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 True
        (Data annz "Bool" [] Type0 True
        (Data annz "Bool.True" [] Type0 False
        (Data annz "Bool.False" [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 "Int"),(Type1 "Int")]) (Type1 "Bool"))
          (If annz
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz "Bool.True" (Unit annz),
                 Cons annz "Bool.False" (Unit annz)]))
            (Nop annz)
            (Nop annz))))))))
      `shouldBe` ["types do not match : expected '(Int,Int)' : found '(Bool.True,Bool.False)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 "Bool")
          (Write annz (LVar "x") (Cons annz{type_=(Type1 "Bool")} "Bool.True" (Unit annz)))))
      `shouldBe` ["type 'Bool' is not declared","type 'Bool.True' is not declared"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz "X" [] (Type1 "Int") False
        (Var annz "x" (Type1 "X")
          (Write annz (LVar "x") (Cons annz "X" (Unit annz))))))
      `shouldBe` ["types do not match : expected 'Int' : found '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz "X" [] (Type1 "Int") False
        (Var annz "x" (Type1 "X")
          (Write annz (LVar "x") (Cons annz "X" (Number annz 1))))))
      `shouldBe` []

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "X"   [] (Type1 "Int") False
        (Data annz "X.Y" [] (Type1 "Int") False
        (Nop annz)))))
      `shouldBe` ([],Data annz "Int" [] Type0 False (Data annz "X" [] (Type1 "Int") False (Data annz "X.Y" [] (TypeN [Type1 "Int",Type1 "Int"]) False (Nop annz))))

    it "data X with (Int,Int))" $
      (fst $ TypeSys.go
        (Data annz "X" [] (TypeN [Type1 "Int", Type1 "Int"]) False
        (Var annz "x" (Type1 "X")
          (Write annz (LVar "x") (Cons annz "X" (Tuple annz [Number annz 1, Number annz 2]))))))
      `shouldBe` []

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
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Class annz "Y" ["a"]
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz "X" ["a"]
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Var annz "f" (TypeF (TypeV "a") Type0)
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz "Equalable" ["a"]
          (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
            (Nop annz))
          (Nop annz))
      `shouldBe` (["type 'Bool' is not declared"],(Class annz "Equalable" ["a"] (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz "Bool" [] Type0 True
        (Class annz "Equalable" ["a"]
          (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool"))
          (Nop annz))
        (Nop annz)))
      `shouldBe` ([],Data annz "Bool" [] Type0 True (Class annz "Equalable" ["a"] (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 "Bool")) (Nop annz)) (Nop annz)))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Nop annz))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff1" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff2" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Nop annz)))))
      `shouldBe` ["names do not match : expected 'fff1' : found 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") (Type1 "Int"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "X" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "Int") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Nop annz))))))
      `shouldBe` ["typeclass 'X' is not declared","variable 'fff' is already declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "Int") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Cons annz "A" (Unit annz)))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [TypeN [Type1 "A", Type1 "A"]]
          (Var annz "fff" (TypeF (TypeN [Type1 "A", Type1 "A"]) Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Tuple annz [(Cons annz "A" (Unit annz)),(Cons annz "A" (Unit annz))])))))
      `shouldBe` ([],Data annz "A" [] Type0 False (Class annz "Xable" ["a"] (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [TypeN [Type1 "A",Type1 "A"]] (Var annz "fff" (TypeF (TypeN [Type1 "A",Type1 "A"]) Type0) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF (TypeN [Type1 "A",Type1 "A"]) Type0} "fff") (Tuple annz{type_=TypeN [Type1 "A",Type1 "A"]} [Cons annz{type_=Type1 "A"} "A" (Unit annz{type_=Type0}),Cons annz{type_=Type1 "A"} "A" (Unit annz{type_=Type0})])))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "A" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Number annz 1)))))))
      `shouldBe` ["variable 'fff' has no associated instance for type '(Int -> ?)' in class 'Xable'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "Bool" [] Type0 False
        (Class annz "Equalable" ["a"]
          (Var annz "eq" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 "Bool")) (Nop annz))
        (CallS annz (Read annz "eq") (Tuple annz [(Cons annz "Bool" (Unit annz)),(Number annz 1)]))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambigous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (TypeSys.go
        (Data annz "Int" [] Type0 False
        (Data annz "Bool" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "Bool"]
          (Var annz "fff" (TypeF (Type1 "Bool") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "Xable" [Type1 "Int"]
          (Var annz "fff" (TypeF (Type1 "Int") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Seq annz
          (CallS annz (Read annz "fff") (Number annz 1))
          (CallS annz (Read annz "fff") (Cons annz "Bool" (Unit annz))))))))))
      `shouldBe` ([],Data annz "Int" [] Type0 False (Data annz "Bool" [] Type0 False (Class annz "Xable" ["a"] (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "Bool"] (Var annz "fff" (TypeF (Type1 "Bool") Type0) (Seq annz (Nop annz) (Nop annz))) (Inst annz "Xable" [Type1 "Int"] (Var annz "fff" (TypeF (Type1 "Int") Type0) (Seq annz (Nop annz) (Nop annz))) (Seq annz (CallS annz (Read annz{type_=TypeF (Type1 "Int") Type0} "fff") (Number annz{type_=Type1 "Int"} 1)) (CallS annz (Read annz{type_=TypeF (Type1 "Bool") Type0} "fff") (Cons annz{type_=Type1 "Bool"} "Bool" (Unit annz{type_=Type0})))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (TypeSys.go
        (Data annz "A" [] Type0 False
        (Data annz "A.B" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Cons annz "A.B" (Unit annz))))))))
      `shouldBe` ([],Data annz "A" [] Type0 False (Data annz "A.B" [] Type0 False (Class annz "Xable" ["a"] (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "A"] (Var annz "fff" (TypeF (Type1 "A") Type0) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF (Type1 "A") Type0} "fff") (Cons annz{type_=Type1 "A.B"} "A.B" (Unit annz{type_=Type0})))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (TypeSys.go
        (Data annz "A" [] Type0 False
        (Data annz "A.B" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "Xable" [Type1 "A.B"]
          (Var annz "fff" (TypeF (Type1 "A.B") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Cons annz "A.B" (Unit annz)))))))))
      `shouldBe` ([],Data annz "A" [] Type0 False (Data annz "A.B" [] Type0 False (Class annz "Xable" ["a"] (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz)) (Inst annz "Xable" [Type1 "A"] (Var annz "fff" (TypeF (Type1 "A") Type0) (Seq annz (Nop annz) (Nop annz))) (Inst annz "Xable" [Type1 "A.B"] (Var annz "fff" (TypeF (Type1 "A.B") Type0) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF (Type1 "A.B") Type0} "fff") (Cons annz{type_=Type1 "A.B"} "A.B" (Unit annz{type_=Type0}))))))))

    it "A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz "A" [] Type0 False
        (Data annz "A.B" [] Type0 False
        (Class annz "Xable" ["a"]
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz "Xable" [Type1 "A.B"]
          (Var annz "fff" (TypeF (Type1 "A.B") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "Xable" [Type1 "A"]
          (Var annz "fff" (TypeF (Type1 "A") Type0)
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Cons annz "A.B" (Unit annz)))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-type polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (TypeSys.go
        (Data annz "B" [] Type0 False
        (Class annz "X" ["b"]
          (Var annz "fff" (TypeF Type0 (TypeV "b")) (Nop annz))
        (Inst annz "X" [Type1 "B"]
          (Var annz "fff" (TypeF Type0 (Type1 "B"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Unit annz))))))
      `shouldBe` ([],Data annz "B" [] Type0 False (Class annz "X" ["b"] (Var annz "fff" (TypeF Type0 (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B"] (Var annz "fff" (TypeF Type0 (Type1 "B")) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF Type0 (Type1 "B")} "fff") (Unit annz{type_=Type0})))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (TypeSys.go
        (Data annz "B" [] Type0 False
        (Class annz "X" ["b"]
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz "X" [Type1 "B"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Unit annz))))))
      `shouldBe` ([],Data annz "B" [] Type0 False (Class annz "X" ["b"] (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B")) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF (TypeV "a") (Type1 "B")} "fff") (Unit annz{type_=Type0})))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (TypeSys.go
        (Data annz "B1" [] Type0 False
        (Data annz "B2" [] Type0 False
        (Class annz "X" ["b"]
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz "X" [Type1 "B1"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "X" [Type1 "B2"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (CallS annz (Read annz "fff") (Unit annz))))))))
      `shouldBe` (["TODO: should be error because both B1/B2 are ok"],
                  -- the problem is that CallS accept any return type
                  Data annz "B1" [] Type0 False (Data annz "B2" [] Type0 False (Class annz "X" ["b"] (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Seq annz (Nop annz) (Nop annz))) (Inst annz "X" [Type1 "B2"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Seq annz (Nop annz) (Nop annz))) (CallS annz (Read annz{type_=TypeF (TypeV "a") (Type1 "B[12]")} "fff") (Unit annz{type_=Type0})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (TypeSys.go
        (Data annz "B1" [] Type0 False
        (Data annz "B2" [] Type0 False
        (Class annz "X" ["b"]
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz "X" [Type1 "B1"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "X" [Type1 "B2"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Var annz "b1" (Type1 "B1")
        (Write annz (LVar "b1")
          (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` ([],Data annz "B1" [] Type0 False (Data annz "B2" [] Type0 False (Class annz "X" ["b"] (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Seq annz (Nop annz) (Nop annz))) (Inst annz "X" [Type1 "B2"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Seq annz (Nop annz) (Nop annz))) (Var annz "b1" (Type1 "B1") (Write annz (LVar "b1") (Call annz{type_=Type1 "B1"} (Read annz{type_=TypeF (TypeV "a") (Type1 "B1")} "fff") (Unit annz{type_=Type0})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (TypeSys.go
        (Data annz "B1" [] Type0 False
        (Data annz "B2" [] Type0 False
        (Class annz "X" ["b"]
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz "X" [Type1 "B1"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Inst annz "X" [Type1 "B2"]
          (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2"))
          (Seq annz
          (Nop annz)
          (Nop annz)))
        (Var annz "b2" (Type1 "B2")
        (Write annz (LVar "b2")
          (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` ([],Data annz "B1" [] Type0 False (Data annz "B2" [] Type0 False (Class annz "X" ["b"] (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz)) (Inst annz "X" [Type1 "B1"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B1")) (Seq annz (Nop annz) (Nop annz))) (Inst annz "X" [Type1 "B2"] (Var annz "fff" (TypeF (TypeV "a") (Type1 "B2")) (Seq annz (Nop annz) (Nop annz))) (Var annz "b2" (Type1 "B2") (Write annz (LVar "b2") (Call annz{type_=Type1 "B2"} (Read annz{type_=TypeF (TypeV "a") (Type1 "B2")} "fff") (Unit annz{type_=Type0})))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
