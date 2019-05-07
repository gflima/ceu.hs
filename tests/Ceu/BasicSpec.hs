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

func id tp p = Var annz id tp
                (Match annz False (LVar id)
                  (Func annz tp (Ret annz (Error annz 99)))
                  p
                  (Ret annz (Error annz 99)))

spec :: Spec
spec = do

  --describe "TODO" $ do

  describe "declarations" $ do

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]))
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]))
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
    checkCheckIt (prelude annz (Var annz "a" (TypeD ["Int"]) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) []
    checkCheckIt (prelude annz (Var annz "a" (TypeN [TypeD ["Int"],TypeD ["Int"]]) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int.1'"]
    --checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match"]
    checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match : expected '()' : found 'Int.1'"]

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" Type0 (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool.True' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Int"]) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool.True' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Bool"]) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Bool"]) (Match annz False (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

    checkCheckIt (Var annz "a" Type0 (Var annz "a" Type0 (Nop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"])) (Var annz "a" (TypeD ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"]))
        (Var annz "a" Type0
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Number annz 1)) (Nop annz) (Nop annz))))))
      `shouldBe` ["types do not match : expected '(Int.1 -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"]))
        (Var annz "a" Type0
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (Match annz False (LVar "a") (Call annz (Read annz "f") (Number annz 1)) (Nop annz) (Nop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0]) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (TypeD ["Int"]) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TypeF (TypeV "a" []) (TypeV "a" [])) (Var annz "a" (TypeD ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "identity") (Number annz 1)) (Nop annz) (Nop annz))))) []

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
        (Var annz "f" (TypeF Type0 (TypeD ["Int"]))
        (Var annz "ret" TypeT
        (Match annz False (LVar "ret") (Call annz (Read annz "f") (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" (TypeD ["Int"])
        (Match annz True (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "ret" (TypeD ["Int"])
        (Match annz False (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TypeF Type0 (TypeD ["Int"])) (Nop annz)))
        `shouldBe` ["data 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))
        `shouldBe` ([],Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (Var annz "f" (TypeF (TypeV "a" []) (TypeV "a" [])) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF (TypeV "a" []) (TypeV "a" [])) (Var annz "f" (TypeF Type0 Type0) (Nop annz)))

    it "func f; func ~f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 TypeT) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF Type0 Type0) (Var annz "f" (TypeF Type0 TypeT) (Nop annz)))

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a" []),(TypeV "a" [])]) (TypeV "a" [])) (Var annz "a" (TypeD ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Unit annz),(Number annz 1)])) (Nop annz) (Nop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambigous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int.1) -> Int)' : found '((a,a) -> a)'","ambigous instances for 'a' : '()', 'Int.1', 'Int'"]

    checkCheckIt (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a" []),(TypeV "a" [])]) (TypeV "a" [])) (Var annz "a" (TypeD ["Int"]) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Number annz 1),(Number annz 1)])) (Nop annz) (Nop annz))))) []

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
        (Var annz "f" (TypeF Type0 (TypeV "a" []))
        (Ret annz (Call annz (Read annz "f") (Unit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Var annz "f" (TypeF (TypeV "a" []) (TypeD ["Int"]))
        (Ret annz (Call annz (Read annz "f") (Number annz 1))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz ["Int"] [] Type0 False
        (Class annz ("X",["a"]) []
            (Var annz "fff" (TypeF (TypeV "a" ["X"]) (TypeD ["Int"])) (Nop annz))
        (Inst annz ("X",[TypeD ["Int"]])
            (Var annz "fff" (TypeF (TypeD ["Int"]) (TypeD ["Int"]))
            (Match annz False
              (LVar "fff")
              (Func annz (TypeF (TypeD ["Int"]) (TypeD ["Int"]))
                (Ret annz (Number annz 1)))
              (Nop annz)
              (Nop annz)))
        (Ret annz (Call annz (Read annz "fff") (Number annz 1)))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (Match annz False (LNumber 1) (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=TypeB} False (LNumber 1) (Number annz{type_=TypeD ["Int","1"]} 1) (Nop annz) (Nop annz))
    it "1 <- 2" $
      TypeSys.go (Match annz True (LNumber 1) (Number annz 2) (Nop annz) (Nop annz))
      `shouldBe` (["types do not match : expected 'Int.1' : found 'Int.2'"],Match annz True (LNumber 1) (Number (annz {type_ = TypeD ["Int","2"]}) 2) (Nop annz) (Nop annz))
    it "_ = 1" $
      TypeSys.go (Match annz False LAny (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=TypeB} False LAny (Number annz{type_=TypeD ["Int","1"]} 1) (Nop annz) (Nop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"])
              (Match annz False (LTuple [LVar "x", LAny]) (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '(?,?)' : found 'Int.1'"],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz{type_=TypeB} "x" (TypeD ["Int"]) (Match annz{type_=TypeB} False (LTuple [LVar "x",LAny]) (Number annz{type_=TypeD ["Int","1"]} 1) (Nop annz) (Nop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"])
              (Match annz False (LTuple [LVar "x", LAny]) (Tuple annz [Number annz 1, Number annz 1]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var (annz{type_ = TypeB}) "x" (TypeD ["Int"]) (Match (annz{type_ = TypeB}) False (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = TypeN [TypeD ["Int","1"],TypeD ["Int","1"]]}) [Number (annz{type_ = TypeD ["Int","1"]}) 1,Number (annz{type_ = TypeD ["Int","1"]}) 1]) (Nop annz) (Nop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"])
              (Var annz "y" (TypeN [Type0, TypeD ["Int"]])
                (Match annz False
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Number annz 1])
                  (Nop annz)
                  (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var (annz{type_ = TypeB}) "x" (TypeD ["Int"]) (Var (annz{type_ = TypeB}) "y" (TypeN [Type0,TypeD ["Int"]]) (Match (annz{type_ = TypeB}) False (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = TypeN [TypeN [Type0,TypeD ["Int"]],TypeD ["Int","1"]]}) [Read (annz{type_ = TypeN [Type0,TypeD ["Int"]]}) "y",Number annz{type_ = TypeD ["Int","1"]} 1]) (Nop annz) (Nop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (TypeD ["Int"]) (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz "a" (TypeD ["Int"]) (Match annz True (LExp $ Read annz{type_ = TypeD ["Int"]} "a") (Number annz{type_=TypeD ["Int","1"]} 1) (Nop annz) (Nop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" Type0 (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int.1'"],Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Data annz ["Bool.True"] [] Type0 False (Data annz ["Bool.False"] [] Type0 False (Var annz "a" Type0 (Match annz True (LExp $ Read annz{type_ = Type0} "a") (Number annz{type_=TypeD ["Int","1"]} 1) (Nop annz) (Nop annz)))))))

    it "data X with Int ; x:Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (Data annz ["Xxx"] [] (TypeD ["Int"]) False (Match annz True (LCons ["Xxx"] (LNumber 1)) (Cons annz ["Xxx"] (Number annz 2)) (Ret annz (Number annz 2)) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (Match annz True (LCons ["A"] LUnit) (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` ["data 'A' is not declared","types do not match : expected 'A' : found 'Int.1'"]

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
        (Var  annz "x" (TypeD ["A","B"])
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
        (Var  annz "x" (TypeN [TypeD ["Int"], TypeD ["A","B"]])
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
      `shouldBe` ["data 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz ["Bool","True","Xxx"] [] Type0 False (Nop annz)))
      `shouldBe` ["data 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Int"] [] Type0 False
        (Nop annz))))
      `shouldBe` ["data 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (TypeD ["Int"]) (Nop annz)))
      `shouldBe` ["data 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
          (Var annz "x" (TypeD ["Bool"])
            (Match annz False (LVar "x") (Cons annz ["Bool"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
          (Var annz "x" (TypeD ["Bool"])
            (Match annz False (LVar "x") (Cons annz ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]))
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Data annz ["Bool","True"] [] Type0 False
        (Data annz ["Bool","False"] [] Type0 False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]))
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
        (Var annz "==" (TypeF (TypeN [(TypeD ["Int"]),(TypeD ["Int"])]) (TypeD ["Bool"]))
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
        (Var annz "x" (TypeD ["Bool"])
          (Match annz False (LVar "x") (Cons annz{type_=(TypeD ["Bool"])} ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (TypeD ["Int"]) False
        (Var annz "x" (TypeD ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (TypeD ["Int"]) False
        (Var annz "x" (TypeD ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["X"]   [] (TypeD ["Int"]) False
        (Data annz ["X","Y"] [] (TypeD ["Int"]) False
        (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] [] Type0 False (Data annz ["X"] [] (TypeD ["Int"]) False (Data annz ["X","Y"] [] (TypeN [TypeD ["Int"],TypeD ["Int"]]) False (Nop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (Data annz ["X"] [] (TypeN [TypeD ["Int"], TypeD ["Int"]]) False
        (Var annz "x" (TypeD ["X"])
          (Match annz False (LVar "x") (Cons annz ["X"] (Tuple annz [Number annz 1, Number annz 2])) (Nop annz) (Nop annz)))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (Data annz ["Int"] [] Type0 False
          (Data annz ["X"] [] (TypeD ["Int"]) False
          (Var annz "x" (TypeD ["Int"])
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (Data annz ["Int"] [] Type0 False
          (Data annz ["X"] [] (TypeD ["Int"]) False
          (Var annz "x" (TypeD ["Int"])
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected 'Int' : found '()'"]

  --------------------------------------------------------------------------

  describe "typeclass:" $ do
    it "X.f ; X.f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) [] (Nop annz)
        (Class annz ("X",["a"]) [] (Nop annz)
        (Nop annz))))
      `shouldBe` ["interface 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) []
          (Var annz "f" (TypeF (TypeV "a" ["X"]) Type0) (Nop annz))
        (Class annz ("Y",["a"]) []
          (Var annz "f" (TypeF (TypeV "a" ["Y"]) Type0) (Nop annz))
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz ("X",["a"]) []
          (Var annz "f" (TypeF (TypeV "a" ["X"]) Type0) (Nop annz))
        (Var annz "f" (TypeF (TypeV "a" []) Type0)
        (Nop annz))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz ("Equalable",["a"]) []
          (Var annz "==" (TypeF (TypeN [(TypeV "a" []),(TypeV "a" [])]) (TypeD ["Bool"]))
            (Nop annz))
          (Nop annz))
      `shouldBe` (["data 'Bool' is not declared"],(Var annz "==" (TypeF (TypeN [TypeV "a" [],TypeV "a" []]) (TypeD ["Bool"])) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Class annz ("Equalable",["a"]) []
          (Var annz "==" (TypeF (TypeN [(TypeV "a" []),(TypeV "a" [])]) (TypeD ["Bool"]))
          (Nop annz))
        (Nop annz)))
      `shouldBe` ([],Data annz ["Bool"] [] Type0 True (Var annz "==" (TypeF (TypeN [TypeV "a" [],TypeV "a" []]) (TypeD ["Bool"])) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz ["Bool"] [] Type0 True
        (Class annz ("Equalable",["a"]) []
          (Var annz "==" (TypeF (TypeN [(TypeV "a" ["Equalable"]),(TypeV "a" ["Equalable"])]) (TypeD ["Bool"]))
          (Nop annz))
        (Nop annz)))
      `shouldBe` ([],Data annz ["Bool"] [] Type0 True (Var annz "==" (TypeF (TypeN [TypeV "a" ["Equalable"],TypeV "a" ["Equalable"]]) (TypeD ["Bool"])) (Nop annz)))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (Var annz "fff" (TypeF (TypeD ["A"]) Type0)
          (Nop annz))
        (Nop annz))))))
      `shouldBe` ["implementation 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff1" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (Nop annz)
        (Nop annz)))))
      `shouldBe` ["missing implementation of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff1" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff2" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (Nop annz)))))
      `shouldBe` ["missing implementation of 'fff1'","unexpected implementation of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff1" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (Nop annz)
        (Nop annz)))))
      `shouldBe` ["missing implementation of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) (TypeD ["Int"])) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("X",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["Int"]) Type0) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["interface 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["Int"]) Type0) (Nop annz))
        (Nop annz))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Cons annz ["A"] (Unit annz))))))))
      `shouldBe` []

    it "XXX: A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeN [TypeD ["A"], TypeD ["A"]]])
          (func "fff" (TypeF (TypeN [TypeD ["A"], TypeD ["A"]]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Tuple annz [(Cons annz ["A"] (Unit annz)),(Cons annz ["A"] (Unit annz))]))))))
      `shouldBe` ([],Data annz ["A"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "__fff__((A,A) -> ())" (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0) (Var annz "__fff__((A,A) -> ())" (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0) (Match annz False (LVar "__fff__((A,A) -> ())") (Func (annz {type_ = TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0}) (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0) (Ret annz (Error annz 99))) (CallS annz (Call (annz {type_ = Type0}) (Read (annz {type_ = TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0}) "__fff__((A,A) -> ())") (Tuple (annz {type_ = TypeN [TypeD ["A"],TypeD ["A"]]}) [Cons (annz {type_ = TypeD ["A"]}) ["A"] (Unit (annz {type_ = Type0})),Cons (annz {type_ = TypeD ["A"]}) ["A"] (Unit (annz {type_ = Type0}))]))) (Ret annz (Error annz 99)))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["A"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable",[TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Number annz 1))))))))
      `shouldBe` []

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Bool"] [] Type0 False
        (Class annz ("Equalable",["a"]) []
          (Var annz "eq" (TypeF (TypeN [(TypeV "a" []),(TypeV "a" [])]) (TypeD ["Bool"])) (Nop annz))
        (CallS annz (Call annz (Read annz "eq") (Tuple annz [(Cons annz ["Bool"] (Unit annz)),(Number annz 1)])))))))
      `shouldBe` ["types do not match : expected '((Bool,Int.1) -> ?)' : found '((a,a) -> Bool)'",
                  "ambigous instances for 'a' : 'Bool', 'Int.1'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (Data annz ["Int"] [] Type0 False
        (Data annz ["Bool"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["Bool"]])
          (func "fff" (TypeF (TypeD ["Bool"]) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["Int"]])
          (func "fff" (TypeF (TypeD ["Int"]) Type0) (Nop annz))
        (Seq annz
          (CallS annz (Call annz (Read annz "fff") (Number annz 1)))
          (CallS annz (Call annz (Read annz "fff") (Cons annz ["Bool"] (Unit annz)))))))))))
      `shouldBe` [] --,Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff__(Bool -> ())" (TypeF (TypeD ["Bool"]) Type0) (Var annz "fff__(Int -> ())" (TypeF (TypeD ["Int"]) Type0) (Seq annz (CallS annz (Call (annz {type_ = Type0}) (Read (annz {type_ = TypeF (TypeD ["Int"]) Type0}) "fff__(Int -> ())") (Number (annz {type_ = TypeD ["Int","1"]}) 1))) (CallS annz (Call (annz {type_ = Type0}) (Read (annz {type_ = TypeF (TypeD ["Bool"]) Type0}) "fff__(Bool -> ())") (Cons (annz {type_ = TypeD ["Bool"]}) ["Bool"] (Unit (annz {type_ = Type0})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable",["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz)))))))))
      `shouldBe` [] --,Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff__(A -> ())" (TypeF (TypeD ["A"]) Type0) (CallS annz (Call (annz {type_ = Type0}) (Read (annz {type_ = TypeF (TypeD ["A"]) Type0}) "fff__(A -> ())") (Cons (annz {type_ = TypeD ["A","B"]}) ["A","B"] (Unit (annz {type_ = Type0})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable", ["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["A","B"]])
          (func "fff" (TypeF (TypeD ["A","B"]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz))))))))))
      `shouldBe` [] --,Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff__(A -> ())" (TypeF (TypeD ["A"]) Type0) (Var annz "fff__(A.B -> ())" (TypeF (TypeD ["A","B"]) Type0) (CallS annz (Call (annz {type_ = Type0}) (Read (annz {type_ = TypeF (TypeD ["A","B"]) Type0}) "fff__(A.B -> ())") (Cons (annz {type_ = TypeD ["A","B"]}) ["A","B"] (Unit (annz {type_ = Type0}))))))))))

    it "A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] [] Type0 False
        (Data annz ["A","B"] [] Type0 False
        (Class annz ("Xable", ["a"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["A","B"]])
          (func "fff" (TypeF (TypeD ["A","B"]) Type0) (Nop annz))
        (Inst annz ("Xable", [TypeD ["A"]])
          (func "fff" (TypeF (TypeD ["A"]) Type0) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF Type0 (TypeV "b" [])) (Nop annz))
        (Inst annz ("X", [TypeD ["B"]])
          (func "fff" (TypeF Type0 (TypeD ["B"])) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Unit annz)))))))
      `shouldBe` [] --,Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF Type0 (TypeV "b" ["X"])) (Var annz "fff__(() -> B)" (TypeF Type0 (TypeD ["B"])) (CallS annz (Call (annz {type_ = TypeD ["B"]}) (Read (annz {type_ = TypeF Type0 (TypeD ["B"])}) "fff__(() -> B)") (Unit (annz {type_ = Type0})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" [])) (Nop annz))
        (Inst annz ("X", [TypeD ["B"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B"])) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Unit annz)))))))
      `shouldBe` [] --,Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff__(a -> B)" (TypeF (TypeV "a" []) (TypeD ["B"])) (CallS annz (Call (annz {type_ = TypeD ["B"]}) (Read (annz {type_ = TypeF (TypeV "a" []) (TypeD ["B"])}) "fff__(a -> B)") (Unit (annz {type_ = Type0})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" [])) (Nop annz))
        (Inst annz ("X", [TypeD ["B1"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Nop annz))
        (Inst annz ("X", [TypeD ["B2"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Nop annz))
        (CallS annz (Call annz (Read annz "fff") (Unit annz)))))))))
                  -- the problem is that CallS accept any return data
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (CallS annz (Call (annz {type_ = TypeD ["B2"]}) (Read (annz {type_ = TypeF (TypeV "a" []) (TypeD ["B2"])}) "fff__(a -> B2)") (Unit (annz {type_ = Type0})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" [])) (Nop annz))
        (Inst annz ("X", [TypeD ["B1"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Nop annz))
        (Inst annz ("X", [TypeD ["B2"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Nop annz))
        (Var annz "b1" (TypeD ["B1"])
        (Match annz False (LVar "b1")
          (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz)))))))))
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b1" (TypeD ["B1"]) (Match annz False (LVar "b1") (Call (annz {type_ = TypeD ["B1"]}) (Read (annz {type_ = TypeF (TypeV "a" []) (TypeD ["B1"])}) "fff__(a -> B1)") (Unit (annz {type_ = Type0}))) (Nop annz) (Nop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] [] Type0 False
        (Data annz ["B2"] [] Type0 False
        (Class annz ("X", ["b"]) []
          (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" [])) (Nop annz))
        (Inst annz ("X", [TypeD ["B1"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Nop annz))
        (Inst annz ("X", [TypeD ["B2"]])
          (func "fff" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Nop annz))
        (Var annz "b2" (TypeD ["B2"])
        (Match annz False (LVar "b2")
          (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz)))))))))
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff__(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff__(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b2" (TypeD ["B2"]) (Match annz False (LVar "b2") (Call (annz {type_ = TypeD ["B2"]}) (Read (annz {type_ = TypeF (TypeV "a" []) (TypeD ["B2"])}) "fff__(a -> B2)") (Unit (annz {type_ = Type0}))) (Nop annz) (Nop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
