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

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 ["Bool"]),(Type1 ["Bool"])]) (Type1 ["Bool"]))
            (CallS annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)])))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 ["Bool"]),(Type1 ["Bool"])]) (Type1 ["Bool"]))
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

  checkCheckIt (Match annz False (LVar "x") (Number annz 0) (Nop annz) (Nop annz)) ["variable 'x' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

    checkCheckIt (Nop annz)                  []
    checkCheckIt (Var annz "a" Type0 (Nop annz))          []
    checkCheckIt (prelude annz (Var annz "a" (Type1 ["Int"]) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) []
    checkCheckIt (prelude annz (Var annz "a" (TypeN [Type1 ["Int"],Type1 ["Int"]]) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int.1'"]
    --checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match"]
    checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match : expected '()' : found 'Int.1'"]

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" Type0 (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool.True' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (Type1 ["Int"]) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool.True' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (Type1 ["Bool"]) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (Type1 ["Bool"]) (Match annz False (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

    checkCheckIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (Var annz "umn" (TypeF (Type1 ["Int"]) (Type1 ["Int"])) (Var annz "a" (Type1 ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
        (Var annz "a" Type0
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Number annz 1)) (Nop annz) (Nop annz))))))
      `shouldBe` ["types do not match : expected '(Int.1 -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
        (Var annz "a" Type0
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (Match annz False (LVar "a") (Call annz (Read annz "f") (Number annz 1)) (Nop annz) (Nop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0]) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (Type1 ["Int"]) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TypeF (TypeV "a") (TypeV "a")) (Var annz "a" (Type1 ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "identity") (Number annz 1)) (Nop annz) (Nop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" TypeT
        (Match annz False (LVar "ret") (Number annz 1) (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" TypeT
        (Match annz True (LVar "ret") (Number annz 1) (Nop annz) (Nop annz)))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "a" TypeT
        (Var annz "b" TypeT
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "a" TypeT
        (Var annz "b" TypeT
        (Match annz True (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "a" TypeT
        (Var annz "b" TypeT
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2,Number annz 3]) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "a" TypeT
        (Var annz "b" TypeT
        (Var annz "c" TypeT
        (Match annz False (LTuple [LVar "a",LVar "b",LVar "c"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz)))))))
        `shouldBe` ["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "f" (TypeF Type0 (Type1 ["Int"]))
        (Var annz "ret" TypeT
        (Match annz False (LVar "ret") (Call annz (Read annz "f") (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" (Type1 ["Int"])
        (Match annz True (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" (Type1 ["Int"])
        (Match annz False (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TypeF Type0 (Type1 ["Int"])) (Nop annz)))
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

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Unit annz),(Number annz 1)])) (Nop annz) (Nop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambigous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int.1) -> Int)' : found '((a,a) -> a)'","ambigous instances for 'a' : '()', 'Int.1', 'Int'"]

    checkCheckIt (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a")) (Var annz "a" (Type1 ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Number annz 1),(Number annz 1)])) (Nop annz) (Nop annz))))) []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 Type0)
        (Match annz False (LVar "f")
          (Func annz (TypeF Type0 Type0)
            (Ret annz (Arg annz)))
          (Nop annz)
          (Nop annz))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 (TypeV "a"))
        (Ret annz (Call annz (Read annz "f") (Unit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "f" (TypeF (TypeV "a") (Type1 ["Int"]))
        (Ret annz (Call annz (Read annz "f") (Number annz 1))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz ["Int"] [] Type0 False
        (Class annz ("X",["a"]) []
            (Var annz "fff" (TypeF (TypeV "a") (Type1 ["Int"])) (Nop annz))
        (Inst annz ("X",[Type1 ["Int"]])
            (Var annz "fff" (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
            (Match annz False
              (LVar "fff")
              (Func annz (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
                (Ret annz (Number annz 1)))
              (Nop annz)
              (Nop annz)))
        (Ret annz (Call annz (Read annz "fff") (Number annz 1)))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (Match annz False (LNumber 1) (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=TypeB} False (LNumber 1) (Number annz{type_=Type1 ["Int","1"]} 1) (Nop annz) (Nop annz))
    it "1 <- 2" $
      TypeSys.go (Match annz True (LNumber 1) (Number annz 2) (Nop annz) (Nop annz))
      `shouldBe` (["types do not match : expected 'Int.1' : found 'Int.2'"],Match annz True (LNumber 1) (Number (annz {type_ = Type1 ["Int","2"]}) 2) (Nop annz) (Nop annz))
    it "_ = 1" $
      TypeSys.go (Match annz False LAny (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=TypeB} False LAny (Number annz{type_=Type1 ["Int","1"]} 1) (Nop annz) (Nop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 ["Int"])
              (Match annz False (LTuple [LVar "x", LAny]) (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '(?,?)' : found 'Int.1'"],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz{type_=TypeB} "x" (Type1 ["Int"]) (Match annz{type_=TypeB} False (LTuple [LVar "x",LAny]) (Number annz{type_=Type1 ["Int","1"]} 1) (Nop annz) (Nop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 ["Int"])
              (Match annz False (LTuple [LVar "x", LAny]) (Tuple annz [Number annz 1, Number annz 1]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var (annz{type_ = TypeB}) "x" (Type1 ["Int"]) (Match (annz{type_ = TypeB}) False (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = TypeN [Type1 ["Int","1"],Type1 ["Int","1"]]}) [Number (annz{type_ = Type1 ["Int","1"]}) 1,Number (annz{type_ = Type1 ["Int","1"]}) 1]) (Nop annz) (Nop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (Type1 ["Int"])
              (Var annz "y" (TypeN [Type0, Type1 ["Int"]])
                (Match annz False
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Number annz 1])
                  (Nop annz)
                  (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var (annz{type_ = TypeB}) "x" (Type1 ["Int"]) (Var (annz{type_ = TypeB}) "y" (TypeN [Type0,Type1 ["Int"]]) (Match (annz{type_ = TypeB}) False (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = TypeN [TypeN [Type0,Type1 ["Int"]],Type1 ["Int","1"]]}) [Read (annz{type_ = TypeN [Type0,Type1 ["Int"]]}) "y",Number annz{type_ = Type1 ["Int","1"]} 1]) (Nop annz) (Nop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (Type1 ["Int"]) (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz "a" (Type1 ["Int"]) (Match annz True (LExp $ Read annz{type_ = Type1 ["Int"]} "a") (Number annz{type_=Type1 ["Int","1"]} 1) (Nop annz) (Nop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" Type0 (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int.1'"],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz "a" Type0 (Match annz True (LExp $ Read annz{type_ = Type0} "a") (Number annz{type_=Type1 ["Int","1"]} 1) (Nop annz) (Nop annz)))))))

    it "data X with Int ; x:Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (Data annz ["Xxx"] [] (Type1 ["Int"]) False (Match annz True (LCons ["Xxx"] (LNumber 1)) (Cons annz ["Xxx"] (Number annz 2)) (Ret annz (Number annz 2)) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (Match annz True (LCons ["A"] LUnit) (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` ["type 'A' is not declared","types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (Data annz ["A"]     [] Type0 True
        (Data annz ["A","B"] [] Type0 False
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (Data annz ["A"]     [] Type0 True
        (Data annz ["A","B"] [] Type0 False
        (Var  annz "x" (Type1 ["A","B"])
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"] (Unit annz)) (Nop annz) (Nop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (Data annz ["A"]     [] Type0 False
        (Data annz ["A","B"] [] Type0 True
        (Match annz True (LCons ["A","B"] LAny) (Cons annz ["A"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (Data annz ["A"] [] Type0 True (Match annz True (LCons ["A"] LUnit) (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (Data annz ["A"] [] Type0 False (Match annz False (LCons ["A"] LUnit) (Cons annz ["A"] (Number annz 1)) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (Data annz ["A"] [] Type0 False (Match annz False (LCons ["A"] (LNumber 1)) (Cons annz ["A"] (Unit annz)) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (Data annz ["Int"]   [] Type0 False
        (Data annz ["A"]     [] Type0 True
        (Data annz ["A","B"] [] Type0 False
        (Var  annz "x" (TypeN [Type1 ["Int"], Type1 ["A","B"]])
        (Match annz True (LTuple [LNumber 1, LCons ["A"] LUnit]) (Read annz "x") (Nop annz) (Nop annz)))))))
      `shouldBe` []

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Data annz ["Int"] [] Type0 False
        (Nop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","False"] [] Type0 False
        (Nop annz)))))
      `shouldBe` ["type 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz ["Bool","True","Xxx"] [] Type0 False (Nop annz)))
      `shouldBe` ["type 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Int"] [] Type0 False
        (Nop annz))))
      `shouldBe` ["type 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 ["Int"]) (Nop annz)))
      `shouldBe` ["type 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
          (Var annz "x" (Type1 ["Bool"])
            (Match annz False (LVar "x") (Cons annz ["Bool"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["type 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
          (Var annz "x" (Type1 ["Bool"])
            (Match annz False (LVar "x") (Cons annz ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 ["Bool"]),(Type1 ["Bool"])]) (Type1 ["Bool"]))
            (CallS annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)])))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 ["Bool"]),(Type1 ["Bool"])]) (Type1 ["Bool"]))
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "Int ; Bool.* ; True <- True==False" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 True
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(Type1 ["Int"]),(Type1 ["Int"])]) (Type1 ["Bool"]))
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"]  (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))
            (Nop annz)
            (Nop annz))))))))
      `shouldBe`
        ["types do not match : expected '((Bool.True,Bool.False) -> ?)' : found '((Int,Int) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (Type1 ["Bool"])
          (Match annz False (LVar "x") (Cons annz{type_=(Type1 ["Bool"])} ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz))))
      `shouldBe` ["type 'Bool' is not declared","type 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (Type1 ["Int"]) False
        (Var annz "x" (Type1 ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (Type1 ["Int"]) False
        (Var annz "x" (Type1 ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["X"]   [] (Type1 ["Int"]) False
        (Data annz ["X","Y"] [] (Type1 ["Int"]) False
        (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["X"] [] (Type1 ["Int"]) False (Data annz ["X","Y"] [] (TypeN [Type1 ["Int"],Type1 ["Int"]]) False (Nop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (TypeN [Type1 ["Int"], Type1 ["Int"]]) False
        (Var annz "x" (Type1 ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Tuple annz [Number annz 1, Number annz 2])) (Nop annz) (Nop annz)))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (Data annz ["Int"] [] Type0 False
          (Data annz ["X"] [] (Type1 ["Int"]) False
          (Var annz "x" (Type1 ["Int"])
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (Data annz ["Int"] [] Type0 False
          (Data annz ["X"] [] (Type1 ["Int"]) False
          (Var annz "x" (Type1 ["Int"])
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected 'Int' : found '()'"]

  --------------------------------------------------------------------------

  describe "typeclass" $ do
    it "X.f ; X.f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) [] (Nop annz)
        (Class annz ("X",["a"]) [] (Nop annz)
        (Nop annz))))
      `shouldBe` ["interface 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) []
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Class annz ("Y",["a"]) []
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) []
          (Var annz "f" (TypeF (TypeV "a") Type0) (Nop annz))
        (Var annz "f" (TypeF (TypeV "a") Type0)
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz ("Equalable",["a"]) []
          (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 ["Bool"]))
            (Nop annz))
          (Nop annz))
      `shouldBe` (["type 'Bool' is not declared"],(Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 ["Bool"])) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Class annz ("Equalable",["a"]) []
          (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 ["Bool"]))
          (Nop annz))
        (Nop annz)))
      `shouldBe` ([],Data annz ["Bool"] [] Type0 True (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (Type1 ["Bool"])) (Nop annz)))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (Nop annz))))))
      `shouldBe` ["missing implementation of 'fff'","instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff1" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff2" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (Nop annz)))))
      `shouldBe` ["missing implementation of 'fff1'","unexpected implementation of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) (Type1 ["Int"]))
          (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'","missing implementation of 'fff'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("X",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["Int"]) Type0)
          (Nop annz))
        (Nop annz))))))
      `shouldBe` ["interface 'X' is not declared","variable 'fff' is already declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["Int"]) Type0)
          (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'","missing implementation of 'fff'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Cons annz ["A"] (Unit annz)))))))
      `shouldBe` ["missing implementation of 'fff'"]

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[TypeN [Type1 ["A"], Type1 ["A"]]])
          (Var annz "fff" (TypeF (TypeN [Type1 ["A"], Type1 ["A"]]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Tuple annz [(Cons annz ["A"] (Unit annz)),(Cons annz ["A"] (Unit annz))])))))
      `shouldBe` (["missing implementation of 'fff'"],Data annz ["A"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") Type0) (Var annz "_inst__Xable__(A,A)" (TypeN [TypeF (TypeN [Type1 ["A"],Type1 ["A"]]) Type0]) (Var annz "fff__((A,A) -> ())" (TypeF (TypeN [Type1 ["A"],Type1 ["A"]]) Type0) (Match annz False (LVar "_inst__Xable__(A,A)") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__((A,A) -> ())"]) (Read annz "_inst__Xable__(A,A)") (CallS annz (Read (annz {type_ = TypeF (TypeN [Type1 ["A"],Type1 ["A"]]) Type0}) "fff__((A,A) -> ())") (Tuple (annz {type_ = TypeN [Type1 ["A"],Type1 ["A"]]}) [Cons (annz {type_ = Type1 ["A"]}) ["A"] (Unit (annz {type_ = Type0})),Cons (annz {type_ = Type1 ["A"]}) ["A"] (Unit (annz {type_ = Type0}))])) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2))))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable",[Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Number annz 1)))))))
      `shouldBe` ["missing implementation of 'fff'","variable 'fff' has no associated instance for type '(Int.1 -> ?)' in class 'Xable'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Bool"] [] Type0 False
        (Class annz ("Equalable",["a"]) []
          (Var annz "eq" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (Type1 ["Bool"])) (Nop annz))
        (CallS annz (Read annz "eq") (Tuple annz [(Cons annz ["Bool"] (Unit annz)),(Number annz 1)]))))))
      `shouldBe` ["types do not match : expected '((Bool,Int.1) -> ?)' : found '((a,a) -> Bool)'",
                  "ambigous instances for 'a' : 'Bool', 'Int.1'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Bool"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable", [Type1 ["Bool"]])
          (Var annz "fff" (TypeF (Type1 ["Bool"]) Type0)
          (Nop annz))
        (Inst annz ("Xable", [Type1 ["Int"]])
          (Var annz "fff" (TypeF (Type1 ["Int"]) Type0)
          (Nop annz))
        (Seq annz
          (CallS annz (Read annz "fff") (Number annz 1))
          (CallS annz (Read annz "fff") (Cons annz ["Bool"] (Unit annz))))))))))
      `shouldBe` (["missing implementation of 'fff'","missing implementation of 'fff'"],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") Type0) (Var annz "_inst__Xable__Bool" (TypeN [TypeF (Type1 ["Bool"]) Type0]) (Var annz "fff__(Bool -> ())" (TypeF (Type1 ["Bool"]) Type0) (Match annz False (LVar "_inst__Xable__Bool") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(Bool -> ())"]) (Read annz "_inst__Xable__Bool") (Var annz "_inst__Xable__Int" (TypeN [TypeF (Type1 ["Int"]) Type0]) (Var annz "fff__(Int -> ())" (TypeF (Type1 ["Int"]) Type0) (Match annz False (LVar "_inst__Xable__Int") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(Int -> ())"]) (Read annz "_inst__Xable__Int") (Seq annz (CallS annz (Read (annz {type_ = TypeF (Type1 ["Int"]) Type0}) "fff__(Int -> ())") (Number (annz {type_ = Type1 ["Int","1"]}) 1)) (CallS annz (Read (annz {type_ = TypeF (Type1 ["Bool"]) Type0}) "fff__(Bool -> ())") (Cons (annz {type_ = Type1 ["Bool"]}) ["Bool"] (Unit (annz {type_ = Type0}))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable", [Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz))))))))
      `shouldBe` (["missing implementation of 'fff'"],Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") Type0) (Var annz "_inst__Xable__A" (TypeN [TypeF (Type1 ["A"]) Type0]) (Var annz "fff__(A -> ())" (TypeF (Type1 ["A"]) Type0) (Match annz False (LVar "_inst__Xable__A") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(A -> ())"]) (Read annz "_inst__Xable__A") (CallS annz (Read (annz {type_ = TypeF (Type1 ["A"]) Type0}) "fff__(A -> ())") (Cons (annz {type_ = Type1 ["A","B"]}) ["A","B"] (Unit (annz {type_ = Type0})))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable", ["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable", [Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (Inst annz ("Xable", [Type1 ["A","B"]])
          (Var annz "fff" (TypeF (Type1 ["A","B"]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz)))))))))
      `shouldBe` (["missing implementation of 'fff'","missing implementation of 'fff'"],Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") Type0) (Var annz "_inst__Xable__A" (TypeN [TypeF (Type1 ["A"]) Type0]) (Var annz "fff__(A -> ())" (TypeF (Type1 ["A"]) Type0) (Match annz False (LVar "_inst__Xable__A") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(A -> ())"]) (Read annz "_inst__Xable__A") (Var annz "_inst__Xable__A.B" (TypeN [TypeF (Type1 ["A","B"]) Type0]) (Var annz "fff__(A.B -> ())" (TypeF (Type1 ["A","B"]) Type0) (Match annz False (LVar "_inst__Xable__A.B") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(A.B -> ())"]) (Read annz "_inst__Xable__A.B") (CallS annz (Read (annz {type_ = TypeF (Type1 ["A","B"]) Type0}) "fff__(A.B -> ())") (Cons (annz {type_ = Type1 ["A","B"]}) ["A","B"] (Unit (annz {type_ = Type0})))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

    it "A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable", ["a"]) []
          (Var annz "fff" (TypeF (TypeV "a") Type0) (Nop annz))
        (Inst annz ("Xable", [Type1 ["A","B"]])
          (Var annz "fff" (TypeF (Type1 ["A","B"]) Type0)
          (Nop annz))
        (Inst annz ("Xable", [Type1 ["A"]])
          (Var annz "fff" (TypeF (Type1 ["A"]) Type0)
          (Nop annz))
        (CallS annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz)))))))))
      `shouldBe` ["TODO: sort by subtyping relation","missing implementation of 'fff'","missing implementation of 'fff'"]

  describe "return-type polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (TypeSys.go
        (Data annz ["B"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF Type0 (TypeV "b")) (Nop annz))
        (Inst annz ("X", [Type1 ["B"]])
          (Var annz "fff" (TypeF Type0 (Type1 ["B"]))
          (Nop annz))
        (CallS annz (Read annz "fff") (Unit annz))))))
      `shouldBe` (["missing implementation of 'fff'"],Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF Type0 (TypeV "b")) (Var annz "_inst__X__B" (TypeN [TypeF Type0 (Type1 ["B"])]) (Var annz "fff__(() -> B)" (TypeF Type0 (Type1 ["B"])) (Match annz False (LVar "_inst__X__B") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(() -> B)"]) (Read annz "_inst__X__B") (CallS annz (Read (annz {type_ = TypeF Type0 (Type1 ["B"])}) "fff__(() -> B)") (Unit (annz {type_ = Type0}))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2))))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (TypeSys.go
        (Data annz ["B"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz ("X", [Type1 ["B"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B"]))
          (Nop annz))
        (CallS annz (Read annz "fff") (Unit annz))))))
      `shouldBe` (["missing implementation of 'fff'"],Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Var annz "_inst__X__B" (TypeN [TypeF (TypeV "a") (Type1 ["B"])]) (Var annz "fff__(a -> B)" (TypeF (TypeV "a") (Type1 ["B"])) (Match annz False (LVar "_inst__X__B") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B)"]) (Read annz "_inst__X__B") (CallS annz (Read (annz {type_ = TypeF (TypeV "a") (Type1 ["B"])}) "fff__(a -> B)") (Unit (annz {type_ = Type0}))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz ("X", [Type1 ["B1"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B1"]))
          (Nop annz))
        (Inst annz ("X", [Type1 ["B2"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B2"]))
          (Nop annz))
        (CallS annz (Read annz "fff") (Unit annz))))))))
      `shouldBe` (["TODO: should be error because both B1/B2 are ok","missing implementation of 'fff'","missing implementation of 'fff'"],
                  -- the problem is that CallS accept any return type
                  Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Var annz "_inst__X__B1" (TypeN [TypeF (TypeV "a") (Type1 ["B1"])]) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a") (Type1 ["B1"])) (Match annz False (LVar "_inst__X__B1") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B1)"]) (Read annz "_inst__X__B1") (Var annz "_inst__X__B2" (TypeN [TypeF (TypeV "a") (Type1 ["B2"])]) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a") (Type1 ["B2"])) (Match annz False (LVar "_inst__X__B2") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B2)"]) (Read annz "_inst__X__B2") (CallS annz (Read (annz {type_ = TypeF (TypeV "a") (Type1 ["B2"])}) "fff__(a -> B2)") (Unit (annz {type_ = Type0}))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz ("X", [Type1 ["B1"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B1"]))
          (Nop annz))
        (Inst annz ("X", [Type1 ["B2"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B2"]))
          (Nop annz))
        (Var annz "b1" (Type1 ["B1"])
        (Match annz False (LVar "b1")
          (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz)))))))))
      `shouldBe` (["missing implementation of 'fff'","missing implementation of 'fff'"],Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Var annz "_inst__X__B1" (TypeN [TypeF (TypeV "a") (Type1 ["B1"])]) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a") (Type1 ["B1"])) (Match annz False (LVar "_inst__X__B1") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B1)"]) (Read annz "_inst__X__B1") (Var annz "_inst__X__B2" (TypeN [TypeF (TypeV "a") (Type1 ["B2"])]) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a") (Type1 ["B2"])) (Match annz False (LVar "_inst__X__B2") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B2)"]) (Read annz "_inst__X__B2") (Var annz "b1" (Type1 ["B1"]) (Match annz False (LVar "b1") (Call (annz {type_ = Type1 ["B1"]}) (Read (annz {type_ = TypeF (TypeV "a") (Type1 ["B1"])}) "fff__(a -> B1)") (Unit (annz {type_ = Type0}))) (Nop annz) (Nop annz))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Nop annz))
        (Inst annz ("X", [Type1 ["B1"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B1"]))
          (Nop annz))
        (Inst annz ("X", [Type1 ["B2"]])
          (Var annz "fff" (TypeF (TypeV "a") (Type1 ["B2"]))
          (Nop annz))
        (Var annz "b2" (Type1 ["B2"])
        (Match annz False (LVar "b2")
          (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz)))))))))
      `shouldBe` (["missing implementation of 'fff'","missing implementation of 'fff'"],Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a") (TypeV "b")) (Var annz "_inst__X__B1" (TypeN [TypeF (TypeV "a") (Type1 ["B1"])]) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a") (Type1 ["B1"])) (Match annz False (LVar "_inst__X__B1") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B1)"]) (Read annz "_inst__X__B1") (Var annz "_inst__X__B2" (TypeN [TypeF (TypeV "a") (Type1 ["B2"])]) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a") (Type1 ["B2"])) (Match annz False (LVar "_inst__X__B2") (Tuple annz [Error annz (-2)]) (Match annz False (LTuple [LVar "fff__(a -> B2)"]) (Read annz "_inst__X__B2") (Var annz "b2" (Type1 ["B2"]) (Match annz False (LVar "b2") (Call (annz {type_ = Type1 ["B2"]}) (Read (annz {type_ = TypeF (TypeV "a") (Type1 ["B2"])}) "fff__(a -> B2)") (Unit (annz {type_ = Type0}))) (Nop annz) (Nop annz))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))) (Ret annz (Error annz (-2)))) (Ret annz (Error annz (-2)))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
