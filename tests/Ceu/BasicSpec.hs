module Ceu.BasicSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (annz, Ann(..))
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..))
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
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]),cz)
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]),cz)
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
    checkCheckIt (Var annz "a" (Type0,cz) (Nop annz))          []
    checkCheckIt (prelude annz (Var annz "a" (TypeD ["Int"],cz) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) []
    checkCheckIt (prelude annz (Var annz "a" (TypeN [TypeD ["Int"],TypeD ["Int"]],cz) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int.1'"]
    --checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match"]
    checkCheckIt (Var annz "a" (Type0,cz) (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))) ["types do not match : expected '()' : found 'Int.1'"]

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (Type0,cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Int"],cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Bool"],cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TypeD ["Bool"],cz) (Match annz False (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

    checkCheckIt (Var annz "a" (Type0,cz) (Var annz "a" (Type0,cz) (Nop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (Match annz False (LVar "a") (Number annz 1) (Nop annz) (Nop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz) (Var annz "a" (TypeD ["Int"],cz) (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz)
        (Var annz "a" (Type0,cz)
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Number annz 1)) (Nop annz) (Nop annz))))))
      `shouldBe` ["types do not match : expected '(Int.1 -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz)
        (Var annz "a" (Type0,cz)
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (Match annz False (LVar "a") (Call annz (Read annz "f") (Number annz 1)) (Nop annz) (Nop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0],cz) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (TypeD ["Int"],cz) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TypeF (TypeV "a") (TypeV "a"),cz) (Var annz "a" (TypeD ["Int"],cz) (Match annz False (LVar "a") (Call annz (Read annz "identity") (Number annz 1)) (Nop annz) (Nop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "ret" (TypeT,cz)
        (Match annz False (LVar "ret") (Number annz 1) (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "ret" (TypeT,cz)
        (Match annz True (LVar "ret") (Number annz 1) (Nop annz) (Nop annz)))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz True (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Number annz 1,Number annz 2,Number annz 3]) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Var annz "c" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b",LVar "c"]) (Tuple annz [Number annz 1,Number annz 2]) (Nop annz) (Nop annz)))))))
        `shouldBe` ["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "f" (TypeF Type0 (TypeD ["Int"]),cz)
        (Var annz "ret" (TypeT,cz)
        (Match annz False (LVar "ret") (Call annz (Read annz "f") (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "ret" (TypeD ["Int"],cz)
        (Match annz True (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "ret" (TypeD ["Int"],cz)
        (Match annz False (LNumber 1) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TypeF Type0 (TypeD ["Int"]),cz) (Nop annz)))
        `shouldBe` ["data 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0,cz) (Var annz "f" (TypeF Type0 Type0,cz) (Nop annz)))
        `shouldBe` ([],Var annz "f" (TypeF Type0 Type0,cz) (Var annz "f" (TypeF Type0 Type0,cz) (Nop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (Var annz "f" (TypeF (TypeV "a") (TypeV "a"),cz) (Var annz "f" (TypeF Type0 Type0,cz) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF (TypeV "a") (TypeV "a"),cz) (Var annz "f" (TypeF Type0 Type0,cz) (Nop annz)))

    it "func f; func ~f" $
      TypeSys.go (Var annz "f" (TypeF Type0 Type0,cz) (Var annz "f" (TypeF Type0 TypeT,cz) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TypeF Type0 Type0,cz) (Var annz "f" (TypeF Type0 TypeT,cz) (Nop annz)))

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a"),cz) (Var annz "a" (TypeD ["Int"],cz) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Unit annz),(Number annz 1)])) (Nop annz) (Nop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambigous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int.1) -> Int)' : found '((a,a) -> a)'","ambigous instances for 'a' : '()', 'Int.1', 'Int'"]

    checkCheckIt (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a"),cz) (Var annz "a" (TypeD ["Int"],cz) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Number annz 1),(Number annz 1)])) (Nop annz) (Nop annz))))) []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 Type0,cz)
        (Match annz False (LVar "f")
          (Func annz (TypeF Type0 Type0,cz)
            (Ret annz (Arg annz)))
          (Nop annz)
          (Nop annz))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (Var annz "f" (TypeF Type0 (TypeV "a"),cz)
        (Ret annz (Call annz (Read annz "f") (Unit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Var annz "f" (TypeF (TypeV "a") (TypeD ["Int"]),cz)
        (Ret annz (Call annz (Read annz "f") (Number annz 1))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz ["Int"] (Type0,cz) False
        (Class annz "X" (cv "a") [(annz,"fff",(TypeF (TypeV "a") (TypeD ["Int"]),cvc ("a","X")),False)]
            (Var annz "fff" (TypeF (TypeV "a") (TypeD ["Int"]),cvc ("a","X"))
        (Inst annz "X" (TypeD ["Int"],cz)
            [(annz,"fff",(TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz),True)]
            (Var annz "fff" (TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz)
            (Match annz False
              (LVar "fff")
              (Func annz (TypeF (TypeD ["Int"]) (TypeD ["Int"]),cz)
                (Ret annz (Number annz 1)))
              (Seq annz
                (Nop annz)
                (Ret annz (Call annz (Read annz "fff") (Number annz 1)))
              )
              (Nop annz))))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (Match annz False (LNumber 1) (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=(TypeB,cz)} False (LNumber 1) (Number annz{type_=(TypeD ["Int","1"],cz)} 1) (Nop annz) (Nop annz))
    it "1 <- 2" $
      TypeSys.go (Match annz True (LNumber 1) (Number annz 2) (Nop annz) (Nop annz))
      `shouldBe` (["types do not match : expected 'Int.1' : found 'Int.2'"],Match annz True (LNumber 1) (Number (annz {type_ = (TypeD ["Int","2"],cz)}) 2) (Nop annz) (Nop annz))
    it "_ = 1" $
      TypeSys.go (Match annz False LAny (Number annz 1) (Nop annz) (Nop annz))
      `shouldBe` ([],Match annz{type_=(TypeB,cz)} False LAny (Number annz{type_=(TypeD ["Int","1"],cz)} 1) (Nop annz) (Nop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"],cz)
              (Match annz False (LTuple [LVar "x", LAny]) (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '(?,?)' : found 'Int.1'"],Data annz ["Int"] (Type0,cz) False (Data annz ["Bool"] (Type0,cz) False (Data annz ["Bool.True"] (Type0,cz) False (Data annz ["Bool.False"] (Type0,cz) False (Var annz{type_=(TypeB,cz)} "x" (TypeD ["Int"],cz) (Match annz{type_=(TypeB,cz)} False (LTuple [LVar "x",LAny]) (Number annz{type_=(TypeD ["Int","1"],cz)} 1) (Nop annz) (Nop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"],cz)
              (Match annz False (LTuple [LVar "x", LAny]) (Tuple annz [Number annz 1, Number annz 1]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] (Type0,cz) False (Data annz ["Bool"] (Type0,cz) False (Data annz ["Bool.True"] (Type0,cz) False (Data annz ["Bool.False"] (Type0,cz) False (Var (annz{type_ = (TypeB,cz)}) "x" (TypeD ["Int"],cz) (Match (annz{type_ = (TypeB,cz)}) False (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = (TypeN [TypeD ["Int","1"],TypeD ["Int","1"]],cz)}) [Number (annz{type_ = (TypeD ["Int","1"],cz)}) 1,Number (annz{type_ = (TypeD ["Int","1"],cz)}) 1]) (Nop annz) (Nop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (TypeD ["Int"],cz)
              (Var annz "y" (TypeN [Type0, TypeD ["Int"]],cz)
                (Match annz False
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Number annz 1])
                  (Nop annz)
                  (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] (Type0,cz) False (Data annz ["Bool"] (Type0,cz) False (Data annz ["Bool.True"] (Type0,cz) False (Data annz ["Bool.False"] (Type0,cz) False (Var (annz{type_ = (TypeB,cz)}) "x" (TypeD ["Int"],cz) (Var (annz{type_ = (TypeB,cz)}) "y" (TypeN [Type0,TypeD ["Int"]],cz) (Match (annz{type_ = (TypeB,cz)}) False (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = (TypeN [TypeN [Type0,TypeD ["Int"]],TypeD ["Int","1"]],cz)}) [Read (annz{type_ = (TypeN [Type0,TypeD ["Int"]],cz)}) "y",Number annz{type_ = (TypeD ["Int","1"],cz)} 1]) (Nop annz) (Nop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (TypeD ["Int"],cz) (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz ["Int"] (Type0,cz) False (Data annz ["Bool"] (Type0,cz) False (Data annz ["Bool.True"] (Type0,cz) False (Data annz ["Bool.False"] (Type0,cz) False (Var annz "a" (TypeD ["Int"],cz) (Match annz True (LExp $ Read annz{type_ = (TypeD ["Int"],cz)} "a") (Number annz{type_=(TypeD ["Int","1"],cz)} 1) (Nop annz) (Nop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (Type0,cz) (Match annz True (LExp $ Read annz "a") (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int.1'"],Data annz ["Int"] (Type0,cz) False (Data annz ["Bool"] (Type0,cz) False (Data annz ["Bool.True"] (Type0,cz) False (Data annz ["Bool.False"] (Type0,cz) False (Var annz "a" (Type0,cz) (Match annz True (LExp $ Read annz{type_ = (Type0,cz)} "a") (Number annz{type_=(TypeD ["Int","1"],cz)} 1) (Nop annz) (Nop annz)))))))

    it "data X with Int ; x:Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (Data annz ["Xxx"] (TypeD ["Int"],cz) False (Match annz True (LCons ["Xxx"] (LNumber 1)) (Cons annz ["Xxx"] (Number annz 2)) (Ret annz (Number annz 2)) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (Match annz True (LCons ["A"] LUnit) (Number annz 1) (Nop annz) (Nop annz)))
      `shouldBe` ["data 'A' is not declared","types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (Data annz ["A"]     (Type0,cz) True
        (Data annz ["A","B"] (Type0,cz) False
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (Data annz ["A"]     (Type0,cz) True
        (Data annz ["A","B"] (Type0,cz) False
        (Var  annz "x" (TypeD ["A","B"],cz)
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"] (Unit annz)) (Nop annz) (Nop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (Data annz ["A"]     (Type0,cz) False
        (Data annz ["A","B"] (Type0,cz) True
        (Match annz True (LCons ["A","B"] LAny) (Cons annz ["A"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (Data annz ["A"] (Type0,cz) True (Match annz True (LCons ["A"] LUnit) (Number annz 1) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (Data annz ["A"] (Type0,cz) False (Match annz False (LCons ["A"] LUnit) (Cons annz ["A"] (Number annz 1)) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (Data annz ["A"] (Type0,cz) False (Match annz False (LCons ["A"] (LNumber 1)) (Cons annz ["A"] (Unit annz)) (Nop annz) (Nop annz))))
      `shouldBe` ["types do not match : expected 'Int' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (Data annz ["Int"]   (Type0,cz) False
        (Data annz ["A"]     (Type0,cz) True
        (Data annz ["A","B"] (Type0,cz) False
        (Var  annz "x" (TypeN [TypeD ["Int"], TypeD ["A","B"]],cz)
        (Match annz True (LTuple [LNumber 1, LCons ["A"] LUnit]) (Read annz "x") (Nop annz) (Nop annz)))))))
      `shouldBe` []

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Data annz ["Int"] (Type0,cz) False
        (Nop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","False"] (Type0,cz) False
        (Nop annz)))))
      `shouldBe` ["data 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz ["Bool","True","Xxx"] (Type0,cz) False (Nop annz)))
      `shouldBe` ["data 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["Int"] (Type0,cz) False
        (Nop annz))))
      `shouldBe` ["data 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (TypeD ["Int"],cz) (Nop annz)))
      `shouldBe` ["data 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
          (Var annz "x" (TypeD ["Bool"],cz)
            (Match annz False (LVar "x") (Cons annz ["Bool"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
          (Var annz "x" (TypeD ["Bool"],cz)
            (Match annz False (LVar "x") (Cons annz ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]),cz)
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"] (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Bool"]),(TypeD ["Bool"])]) (TypeD ["Bool"]),cz)
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
        (Data annz ["Int"] (Type0,cz) True
        (Data annz ["Bool"] (Type0,cz) True
        (Data annz ["Bool","True"] (Type0,cz) False
        (Data annz ["Bool","False"] (Type0,cz) False
        (Var annz "==" (TypeF (TypeN [(TypeD ["Int"]),(TypeD ["Int"])]) (TypeD ["Bool"]),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"]  (Unit annz),
                 Cons annz ["Bool","False"] (Unit annz)]))
            (Nop annz)
            (Nop annz))))))))
      `shouldBe`
        ["types do not match : expected '((Bool.True,Bool.False) -> Bool)' : found '((Int,Int) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (TypeD ["Bool"],cz)
          (Match annz False (LVar "x") (Cons annz{type_=(TypeD ["Bool"],cz)} ["Bool","True"] (Unit annz)) (Nop annz) (Nop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (Data annz ["X"] (TypeD ["Int"],cz) False
        (Var annz "x" (TypeD ["X"],cz)
          (Match annz False (LVar "x") (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz ["X"] (TypeD ["Int"],cz) False
        (Var annz "x" (TypeD ["X"],cz)
          (Match annz False (LVar "x") (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["X"]   (TypeD ["Int"],cz) False
        (Data annz ["X","Y"] (TypeD ["Int"],cz) False
        (Nop annz)))))
      `shouldBe` ([],Data annz ["Int"] (Type0,cz) False (Data annz ["X"] (TypeD ["Int"],cz) False (Data annz ["X","Y"] (TypeN [TypeD ["Int"],TypeD ["Int"]],cz) False (Nop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (Data annz ["X"] (TypeN [TypeD ["Int"], TypeD ["Int"]],cz) False
        (Var annz "x" (TypeD ["X"],cz)
          (Match annz False (LVar "x") (Cons annz ["X"] (Tuple annz [Number annz 1, Number annz 2])) (Nop annz) (Nop annz)))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (Data annz ["Int"] (Type0,cz) False
          (Data annz ["X"] (TypeD ["Int"],cz) False
          (Var annz "x" (TypeD ["Int"],cz)
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Number annz 1)) (Nop annz) (Nop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (Data annz ["Int"] (Type0,cz) False
          (Data annz ["X"] (TypeD ["Int"],cz) False
          (Var annz "x" (TypeD ["Int"],cz)
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"] (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected 'Int' : found '()'"]

  --------------------------------------------------------------------------

  describe "typeclass:" $ do
    it "X.f ; X.f" $
      (fst $ TypeSys.go
        (Class annz "X" (cv "a") []
        (Class annz "X" (cv "a") []
        (Nop annz))))
      `shouldBe` ["constraint 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst $ TypeSys.go
        (Class annz "X" (cv "a") []
        (Var annz "f" (TypeF (TypeV "a") Type0,cvc ("a","X"))
        (Class annz "Y" (cv "a") []
        (Var annz "f" (TypeF (TypeV "a") Type0,cvc ("a","Y"))
        (Nop annz))))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz "X" (cv "a") []
        (Var annz "f" (TypeF (TypeV "a") Type0, cvc ("a","X"))
        (Var annz "f" (TypeF (TypeV "a") Type0,cz)
        (Nop annz)))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeD ["Bool"]),cz)
        (Nop annz)))
      `shouldBe` (["data 'Bool' is not declared"],(Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeD ["Bool"]),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeD ["Bool"]),cz)
        (Nop annz))))
      `shouldBe` ([],Data annz ["Bool"] (Type0,cz) True (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeD ["Bool"]),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz ["Bool"] (Type0,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeD ["Bool"]), cvc ("a","Equalable"))
        (Nop annz))))
      `shouldBe` ([],Data annz ["Bool"] (Type0,cz) True (Nop annz))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz, "fff", (TypeF (TypeD ["A"]) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A"],cz)
                [(annz,"fff",(TypeF (TypeD ["A"]) Type0,cz),True)]
                (Var annz "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
                (Seq annz
                  (Nop annz)
                  (Nop annz))))
            )))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz,"fff2",(TypeF (TypeD ["A"]) Type0,cz),True)]
          (func "fff2" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Nop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz,"fff",(TypeF (TypeD ["A"]) (TypeD ["Int"]),cz),True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) (TypeD ["Int"]),cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "X" (TypeD ["A"],cz)
          [(annz,"fff",(TypeF (TypeD ["Int"]) Type0,cz),True)]
          (func "$fff$(Int -> ())$" (TypeF (TypeD ["Int"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
          (Var annz "fff" (TypeF (TypeV "a") Type0,cz)        -- a
        (Inst annz "Xable" (TypeD ["A"],cz)                          -- A
          [(annz, "fff", (TypeF (TypeD ["Int"]) Type0,cz), True)]
          (func "$fff$(Int -> ())$" (TypeF (TypeD ["Int"]) Type0,cz)  -- Int
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz,"fff",(TypeF (TypeD ["A"]) Type0,cz),True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Cons annz ["A"] (Unit annz)))))))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0, cvc ("a","Xable"))
        (Inst annz "Xable" (TypeN [TypeD ["A"], TypeD ["A"]],cz)
          [(annz, "fff", (TypeF (TypeN [TypeD ["A"], TypeD ["A"]]) Type0,cz), True)]
          (func "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"], TypeD ["A"]]) Type0,cz)
            (CallS annz (Call annz (Read annz "fff") (Tuple annz [(Cons annz ["A"] (Unit annz)),(Cons annz ["A"] (Unit annz))]))))))))
      `shouldBe` ([],
        Data annz ["A"] (Type0,cz) False
        (Var annz "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0,cz)
        (Var annz "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0,cz)
        (Match annz False (LVar "$fff$((A,A) -> ())$")
          (Func (annz {type_ = (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0,cz)}) (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0,cz) (Ret annz (Error annz 99)))
          (CallS annz
            (Call (annz {type_ = (Type0,cz)})
              (Read (annz {type_ = (TypeF (TypeN [TypeD ["A"],TypeD ["A"]]) Type0,cz)}) "$fff$((A,A) -> ())$")
              (Tuple
                (annz {type_ = (TypeN [TypeD ["A"],TypeD ["A"]],cz)}) [Cons (annz {type_ = (TypeD ["A"],cz)}) ["A"] (Unit (annz {type_ = (Type0,cz)})),Cons (annz {type_ = (TypeD ["A"],cz)}) ["A"] (Unit (annz {type_ = (Type0,cz)}))])))
          (Ret annz (Error annz 99))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["A"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0, cvc ("a","Xable")),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0, cvc ("a","Xable"))
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz, "fff", (TypeF (TypeD ["A"]) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Number annz 1)))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int.1 -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["Bool"] (Type0,cz) False
        (Class annz "Equalable" (cv "a") [(annz,"eq",(TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeD ["Bool"]),cz),False)]
        (Var annz "eq" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeD ["Bool"]),cz)
        (CallS annz (Call annz (Read annz "eq") (Tuple annz [(Cons annz ["Bool"] (Unit annz)),(Number annz 1)]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int.1) -> ?)' : found '((a,a) -> Bool)'",
                  "ambigous instances for 'a' : 'Bool', 'Int.1'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (Data annz ["Int"] (Type0,cz) False
        (Data annz ["Bool"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["Bool"],cz)
          [(annz, "fff", (TypeF (TypeD ["Bool"]) Type0,cz), True)]
          (func "$fff$(Bool -> ())$" (TypeF (TypeD ["Bool"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["Int"],cz)
                [(annz, "fff", (TypeF (TypeD ["Int"]) Type0,cz), True)]
                (func "$fff$(Int -> ())$" (TypeF (TypeD ["Int"]) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (Seq annz
                      (CallS annz (Call annz (Read annz "fff") (Number annz 1)))
                      (CallS annz (Call annz (Read annz "fff") (Cons annz ["Bool"] (Unit annz))))))))))))))))
      `shouldBe` [] --,Data annz ["Int"] [] Type0 False (Data annz ["Bool"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(Bool -> ())" (TypeF (TypeD ["Bool"]) Type0) (Var annz "fff$(Int -> ())" (TypeF (TypeD ["Int"]) Type0) (Seq annz (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["Int"]) Type0,[]}) "fff$(Int -> ())") (Number (annz {type_ = (TypeD ["Int","1"],[]}) 1))) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["Bool"]) Type0,[]}) "fff$(Bool -> ())") (Cons (annz {type_ = (TypeD ["Bool"],[]}) ["Bool"] (Unit (annz {type_ = (Type0,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Data annz ["A","B"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz, "fff", (TypeF (TypeD ["A"]) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz))))))))))))
      `shouldBe` [] --,Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(A -> ())" (TypeF (TypeD ["A"]) Type0) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["A"]) Type0,[]}) "fff$(A -> ())") (Cons (annz {type_ = (TypeD ["A","B"],[]}) ["A","B"] (Unit (annz {type_ = (Type0,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Data annz ["A","B"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"],cz)
          [(annz, "fff", (TypeF (TypeD ["A"]) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A","B"],cz)
                [(annz, "fff", (TypeF (TypeD ["A","B"]) Type0,cz), True)]
                (func "$fff$((A,B) -> ())$" (TypeF (TypeD ["A","B"]) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz)))))))))))))))
      `shouldBe` [] --,Data annz ["A"] [] Type0 False (Data annz ["A","B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(A -> ())" (TypeF (TypeD ["A"]) Type0) (Var annz "fff$(A.B -> ())" (TypeF (TypeD ["A","B"]) Type0) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["A","B"]) Type0,[]}) "fff$(A.B -> ())") (Cons (annz {type_ = (TypeD ["A","B"],[]}) ["A","B"] (Unit (annz {type_ = (Type0,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz ["A"] (Type0,cz) False
        (Data annz ["A","B"] (Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A","B"],cz)
          [(annz, "fff", (TypeF (TypeD ["A","B"]) Type0,cz), True)]
          (func "$fff$((A,B) -> ())$" (TypeF (TypeD ["A","B"]) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A"],cz)
                [(annz, "fff", (TypeF (TypeD ["A"]) Type0,cz), True)]
                (func "$fff$(A -> ())$" (TypeF (TypeD ["A"]) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"] (Unit annz)))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B"] (Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF Type0 (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF Type0 (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B"],cz)
          [(annz, "fff", (TypeF Type0 (TypeD ["B"]),cz), True)]
          (func "$fff$(() -> B)$" (TypeF Type0 (TypeD ["B"]),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF Type0 (TypeV "b" ["X"])) (Var annz "fff$(() -> B)" (TypeF Type0 (TypeD ["B"])) (CallS annz (Call (annz {type_ = (TypeD ["B"],[]}) (Read (annz {type_ = (TypeF Type0 (TypeD ["B"]),[]}) "fff$(() -> B)") (Unit (annz {type_ = (Type0,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B"] (Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B"],cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B"]),cz), True)]
          (func "$fff$(a -> B)$" (TypeF (TypeV "a") (TypeD ["B"]),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B)" (TypeF (TypeV "a" []) (TypeD ["B"])) (CallS annz (Call (annz {type_ = (TypeD ["B"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B"]),[]}) "fff$(a -> B)") (Unit (annz {type_ = (Type0,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] (Type0,cz) False
        (Data annz ["B2"] (Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"],cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"]),cz), True)]
          (func "$fff$(a -> B)$" (TypeF (TypeV "a") (TypeD ["B1"]),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"],cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"]),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"]),cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))))))
                  -- the problem is that CallS accept any return data
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (CallS annz (Call (annz {type_ = (TypeD ["B2"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B2"]),[]}) "fff$(a -> B2)") (Unit (annz {type_ = (Type0,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] (Type0,cz) False
        (Data annz ["B2"] (Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"],cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"]),cz), True)]
          (func "$fff$(a -> B1)$" (TypeF (TypeV "a") (TypeD ["B1"]),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"],cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"]),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"]),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b1" (TypeD ["B1"],cz)
                    (Match annz False (LVar "b1")
                      (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b1" (TypeD ["B1"]) (Match annz False (LVar "b1") (Call (annz {type_ = (TypeD ["B1"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B1"]),[]}) "fff$(a -> B1)") (Unit (annz {type_ = (Type0,[]}))) (Nop annz) (Nop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (Data annz ["B1"] (Type0,cz) False
        (Data annz ["B2"] (Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"],cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"]),cz), True)]
          (func "$fff$(a -> B1)$" (TypeF (TypeV "a") (TypeD ["B1"]),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"],cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"]),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"]),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b2" (TypeD ["B2"],cz)
                    (Match annz False (LVar "b2")
                      (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] Type0 False (Data annz ["B2"] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b2" (TypeD ["B2"]) (Match annz False (LVar "b2") (Call (annz {type_ = (TypeD ["B2"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B2"]),[]}) "fff$(a -> B2)") (Unit (annz {type_ = (Type0,[]}))) (Nop annz) (Nop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
