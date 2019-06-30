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

int   = TypeD ["Int"]          [] Type0
bool  = TypeD ["Bool"]         [] Type0
boolf = TypeD ["Bool","False"] [] Type0
boolt = TypeD ["Bool","True"]  [] Type0

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
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TypeF (TypeN [(bool),(bool)]) (bool),cz)
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"],
                 Cons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TypeF (TypeN [(bool),(bool)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"],
                 Cons annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "x <- 0" $
      (fst $ TypeSys.go (Match annz False (LVar "x") (Cons annz ["Int","0"]) (Nop annz) (Nop annz)))
        `shouldBe` ["variable 'x' is not declared","data 'Int.0' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

    checkCheckIt (Nop annz)                  []
    checkCheckIt (prelude annz (Var annz "a" (TypeN [int,int],cz) (Match annz False (LVar "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int'"]
    --checkCheckIt (Var annz "a" Type0 (Match annz False (LVar "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz))) ["types do not match"]
    checkCheckIt (prelude annz (Var annz "a" (Type0,cz) (Match annz False (LVar "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))) ["types do not match : expected '()' : found 'Int'"]

    it "a <- 1" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (int,cz) (Match annz False (LVar "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` []

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (Type0,cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (int,cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (bool,cz) (Match annz True (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (bool,cz) (Match annz False (LCons ["Bool","True"] LUnit) (Read annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

    checkCheckIt (Var annz "a" (Type0,cz) (Var annz "a" (Type0,cz) (Nop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (prelude annz $ Match annz False (LVar "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (Var annz "umn" (TypeF (int) (int),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (int) (int),cz)
        (Var annz "a" (Type0,cz)
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Cons annz ["Int","1"])) (Nop annz) (Nop annz))))))
      `shouldBe` ["types do not match : expected '(Int -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TypeF (int) (int),cz)
        (Var annz "a" (Type0,cz)
        (Match annz False (LVar "a") (Call annz (Read annz "umn") (Read annz "b")) (Nop annz) (Nop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (prelude annz $ Match annz False (LVar "a") (Call annz (Read annz "f") (Cons annz ["Int","1"])) (Nop annz) (Nop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TypeN [Type0,Type0],cz) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (int,cz) (Match annz False (LVar "x") (Unit annz) (Nop annz) (Nop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TypeF (TypeV "a") (TypeV "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (Call annz (Read annz "identity") (Cons annz ["Int","1"])) (Nop annz) (Nop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (TypeT,cz)
        (Match annz False (LVar "ret") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (TypeT,cz)
        (Match annz True (LVar "ret") (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"]]) (Nop annz) (Nop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz True (LTuple [LVar "a",LVar "b"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"]]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"],Cons annz ["Int","3"]]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TypeT,cz)
        (Var annz "b" (TypeT,cz)
        (Var annz "c" (TypeT,cz)
        (Match annz False (LTuple [LVar "a",LVar "b",LVar "c"]) (Tuple annz [Cons annz ["Int","1"],Cons annz ["Int","2"]]) (Nop annz) (Nop annz)))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "f" (TypeF Type0 (int),cz)
        (Var annz "ret" (TypeT,cz)
        (Match annz False (LVar "ret") (Call annz (Read annz "f") (Unit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (int,cz)
        (Match annz True (LCons ["Int","1"] LUnit) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (int,cz)
        (Match annz False (LCons ["Int","1"] LUnit) (Read annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TypeF Type0 (int),cz) (Nop annz)))
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
      (fst $ TypeSys.go (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Unit annz),(Cons annz ["Int","1"])])) (Nop annz) (Nop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambiguous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous instances for 'a' : '()', 'Int', 'Int'"]

{-
    checkCheckIt (prelude annz (Var annz "first" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (TypeV "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (Call annz (Read annz "first") (Tuple annz [(Cons annz ["Int","1"]),(Cons annz ["Int","1"])])) (Nop annz) (Nop annz))))) []
-}

    it "() <- Arg" $
      (fst $ TypeSys.go
        (Match annz False LUnit (Arg annz) (Nop annz) (Nop annz)))
      `shouldBe` []

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
        (Data annz (int,cz) False
        (Var annz "f" (TypeF (TypeV "a") (int),cz)
        (Ret annz (Call annz (Read annz "f") (Cons annz ["Int","1"]))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz (int,cz) False
        (Class annz "X" (cv "a") [(annz,"fff",(TypeF (TypeV "a") (int),cvc ("a","X")),False)]
            (Var annz "fff" (TypeF (TypeV "a") (int),cvc ("a","X"))
        (Inst annz "X" (int,cz)
            [(annz,"fff",(TypeF (int) (int),cz),True)]
            (Var annz "fff" (TypeF (int) (int),cz)
            (Match annz False
              (LVar "fff")
              (Func annz (TypeF (int) (int),cz)
                (Ret annz (Cons annz ["Int","1"])))
              (Seq annz
                (Nop annz)
                (Ret annz (Call annz (Read annz "fff") (Cons annz ["Int","1"])))
              )
              (Nop annz))))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (prelude annz $ Match annz False (LCons ["Int","1"] LUnit) (Cons annz ["Int","1"]) (Nop annz) (Nop annz))
      `shouldBe` ([],Data annz (TypeD ["Int"] [] Type0,cz) False (Data annz (TypeD ["Bool"] [] Type0,cz) False (Data annz (TypeD ["Bool","True"] [] Type0,cz) False (Data annz (TypeD ["Bool","False"] [] Type0,cz) False (Match annz{type_=(TypeB,cz)} False (LCons ["Int","1"] LUnit) (Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (Nop annz) (Nop annz))))))
    it "1 <- 2" $
      TypeSys.go (prelude annz $ Match annz True (LCons ["Int","1"] LUnit) (Cons annz ["Int","2"]) (Nop annz) (Nop annz))
      `shouldBe` (["match never succeeds : data mismatch"],Data annz (TypeD ["Int"] [] Type0,cz) False (Data annz (TypeD ["Bool"] [] Type0,cz) False (Data annz (TypeD ["Bool","True"] [] Type0,cz) False (Data annz (TypeD ["Bool","False"] [] Type0,cz) False (Match annz True (LCons ["Int","1"] LUnit) (Cons (annz {type_ = (TypeD ["Int"] [] Type0,cz)}) ["Int","2"]) (Nop annz) (Nop annz))))))
    it "_ = 1" $
      TypeSys.go (Match annz False LAny (Cons annz ["Int","1"]) (Nop annz) (Nop annz))
      `shouldBe` (["data 'Int.1' is not declared"],Match annz{type_=(TypeB,cz)} False LAny (Cons annz{type_=(TypeV "?",cz)} ["Int","1"]) (Nop annz) (Nop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Match annz False (LTuple [LVar "x", LAny]) (Cons annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` (["match never succeeds"],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz{type_=(TypeB,cz)} "x" (int,cz) (Match annz{type_=(TypeB,cz)} False (LTuple [LVar "x",LAny]) (Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Match annz False (LTuple [LVar "x", LAny]) (Tuple annz [Cons annz ["Int","1"], Cons annz ["Int","1"]]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var (annz{type_ = (TypeB,cz)}) "x" (int,cz) (Match (annz{type_ = (TypeB,cz)}) False (LTuple [LVar "x",LAny]) (Tuple (annz{type_ = (TypeN [TypeD ["Int"] [] Type0,TypeD ["Int"] [] Type0],cz)}) [Cons (annz{type_ = (TypeD ["Int"] [] Type0,cz)}) ["Int","1"],Cons (annz{type_ = (TypeD ["Int"] [] Type0,cz)}) ["Int","1"]]) (Nop annz) (Nop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Var annz "y" (TypeN [Type0, int],cz)
                (Match annz False
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (Tuple annz [Read annz "y", Cons annz ["Int","1"]])
                  (Nop annz)
                  (Nop annz)))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var (annz{type_ = (TypeB,cz)}) "x" (int,cz) (Var (annz{type_ = (TypeB,cz)}) "y" (TypeN [Type0,int],cz) (Match (annz{type_ = (TypeB,cz)}) False (LTuple [LTuple [LAny,LVar "x"],LAny]) (Tuple (annz{type_ = (TypeN [TypeN [Type0,int],TypeD ["Int"] [] Type0],cz)}) [Read (annz{type_ = (TypeN [Type0,int],cz)}) "y",Cons annz{type_ = (TypeD ["Int"] [] Type0,cz)} ["Int","1"]]) (Nop annz) (Nop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (int,cz) (Match annz True (LExp $ Read annz "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz "a" (int,cz) (Match annz True (LExp $ Read annz{type_ = (int,cz)} "a") (Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (Type0,cz) (Match annz True (LExp $ Read annz "a") (Cons annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz "a" (Type0,cz) (Match annz True (LExp $ Read annz{type_ = (Type0,cz)} "a") (Cons annz{type_=(TypeD ["Int"] [] Type0,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))

    it "data X with Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (Data annz (TypeD ["Xxx"] [] int,cz) False (Match annz True (LCons ["Xxx"] (LCons ["Int","1"] LUnit)) (Call annz (Cons annz ["Xxx"]) (Cons annz ["Int","2"])) (Ret annz (Cons annz ["Int","2"])) (Nop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (Match annz True (LCons ["A"] LUnit) (Cons annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` ["data 'A' is not declared","match never succeeds : data mismatch"] --"types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) True
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"]) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"]     [] Type0,cz) True
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Var  annz "x" (TypeD ["A","B"] [] Type0,cz)
        (Match annz False (LCons ["A"] LAny) (Cons annz ["A","B"]) (Nop annz) (Nop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"]     [] Type0,cz) False
        (Data annz (TypeD ["A","B"] [] Type0,cz) True
        (Match annz True (LCons ["A","B"] LAny) (Cons annz ["A"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (Data annz (TypeD ["A"] [] Type0,cz) True (Match annz True (LCons ["A"] LUnit) (Cons annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds : data mismatch"] --["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (Data annz (TypeD ["A"] [] Type0,cz) False (Match annz False (LCons ["A"] LUnit) (Call annz (Cons annz ["A"]) (Cons annz ["Int","1"])) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (prelude annz $ Data annz (TypeD ["A"] [] Type0,cz) False (Match annz False (LCons ["A"] (LCons ["Int","1"] LUnit)) (Cons annz ["A"]) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["A"] [] Type0,cz) True
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Var  annz "x" (TypeN [int, TypeD ["A","B"] [] Type0],cz)
        (Match annz True (LTuple [LCons ["Int","1"] LUnit, LCons ["A"] LUnit]) (Read annz "x") (Nop annz) (Nop annz)))))))
      `shouldBe` []

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Data annz (int,cz) False
        (Nop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz (boolt,cz) False
        (Data annz (bool,cz) True
        (Data annz (boolf,cz) False
        (Nop annz)))))
      `shouldBe` ["data 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["Bool","True","Xxx"] [] Type0,cz) False (Nop annz)))
      `shouldBe` ["data 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (int,cz) False
        (Nop annz))))
      `shouldBe` ["data 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (Var annz "x" (int,cz) (Nop annz)))
      `shouldBe` ["data 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
          (Var annz "x" (bool,cz)
            (Match annz False (LVar "x") (Cons annz ["Bool"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
          (Var annz "x" (bool,cz)
            (Match annz False (LVar "x") (Cons annz ["Bool","True"]) (Nop annz) (Nop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TypeF (TypeN [(bool),(bool)]) (bool),cz)
            (CallS annz (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"],
                 Cons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TypeF (TypeN [(bool),(bool)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"],
                 Cons annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "Int ; Bool.* ; True <- True==False" $
      (fst $ TypeSys.go
        (Data annz (int,cz) True
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TypeF (TypeN [(int),(int)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (Call annz (Read annz "==")
              (Tuple annz
                [Cons annz ["Bool","True"],
                 Cons annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz))))))))
      `shouldBe`
        ["types do not match : expected '((Bool.True,Bool.False) -> Bool)' : found '((Int,Int) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (bool,cz)
          (Match annz False (LVar "x") (Cons annz{type_=(bool,cz)} ["Bool","True"]) (Nop annz) (Nop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["X"] [] int,cz) False
        (Var annz "x" (TypeD ["X"] [] Type0,cz)
          (Match annz False (LVar "x") (Cons annz ["X"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'X' : found '(Int -> X)'"]
      --["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["X"] [] int,cz) False
        (Var annz "x" (TypeD ["X"] [] (int),cz)
          (Match annz False (LVar "x") (Call annz (Cons annz ["X"]) (Cons annz ["Int","1"])) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Int' is not declared","data 'Int.1' is not declared"]

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["X"]     [] int,cz) False
        (Data annz (TypeD ["X","Y"] [] int,cz) False
        (Nop annz)))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (TypeD ["X"] [] int,cz) False (Data annz (TypeD ["X","Y"] [] int,cz) False (Nop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["X"] [] (TypeN [int, int]),cz) False
        (Var annz "x" (TypeD ["X"] [] (TypeN [int, int]),cz)
          (Match annz False (LVar "x") (Call annz (Cons annz ["X"]) (Tuple annz [Cons annz ["Int","1"], Cons annz ["Int","2"]])) (Nop annz) (Nop annz))))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (Data annz (int,cz) False
          (Data annz (TypeD ["X"] [] int,cz) False
          (Var annz "x" (int,cz)
          (Match annz False (LCons ["X"] (LVar "x")) (Call annz (Cons annz ["X"]) (Cons annz ["Int","1"])) (Nop annz) (Nop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (Data annz (int,cz) False
          (Data annz (TypeD ["X"] [] int,cz) False
          (Var annz "x" (int,cz)
          (Match annz False (LCons ["X"] (LVar "x")) (Cons annz ["X"]) (Nop annz) (Nop annz))))))
        `shouldBe` ["types do not match : expected 'X' : found '(Int -> X)'"]
          --["types do not match : expected 'Int' : found '()'"]

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
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (bool),cz)
        (Nop annz)))
      `shouldBe` (["data 'Bool' is not declared"],(Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz (bool,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (bool),cz)
        (Nop annz))))
      `shouldBe` ([],Data annz (bool,cz) True (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz (bool,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (bool), cvc ("a","Equalable"))
        (Nop annz))))
      `shouldBe` ([],Data annz (bool,cz) True (Nop annz))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeD ["A"] [] Type0) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
                [(annz,"fff",(TypeF (TypeD ["A"] [] Type0) Type0,cz),True)]
                (Var annz "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
                (Seq annz
                  (Nop annz)
                  (Nop annz))))
            )))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz,"fff2",(TypeF (TypeD ["A"] [] Type0) Type0,cz),True)]
          (func "fff2" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (Nop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff1" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz,"fff",(TypeF (TypeD ["A"] [] Type0) (int),cz),True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) (int),cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "X" (TypeD ["A"] [] Type0,cz)
          [(annz,"fff",(TypeF (int) Type0,cz),True)]
          (func "$fff$(Int -> ())$" (TypeF (int) Type0,cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
          (Var annz "fff" (TypeF (TypeV "a") Type0,cz)        -- a
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)                          -- A
          [(annz, "fff", (TypeF (int) Type0,cz), True)]
          (func "$fff$(Int -> ())$" (TypeF (int) Type0,cz)  -- Int
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz,"fff",(TypeF (TypeD ["A"] [] Type0) Type0,cz),True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Cons annz ["A"]))))))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0, cvc ("a","Xable"))
        (Inst annz "Xable" (TypeN [TypeD ["A"] [] Type0, TypeD ["A"] [] Type0],cz)
          [(annz, "fff", (TypeF (TypeN [TypeD ["A"] [] Type0, TypeD ["A"] [] Type0]) Type0,cz), True)]
          (func "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"] [] Type0, TypeD ["A"] [] Type0]) Type0,cz)
            (CallS annz (Call annz (Read annz "fff") (Tuple annz [(Cons annz ["A"]),(Cons annz ["A"])]))))))))
      `shouldBe` ([],
        Data annz (TypeD ["A"] [] Type0,cz) False
        (Var annz "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0]) Type0,cz)
        (Var annz "$fff$((A,A) -> ())$" (TypeF (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0]) Type0,cz)
        (Match annz False (LVar "$fff$((A,A) -> ())$")
          (Func (annz {type_ = (TypeF (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0]) Type0,cz)}) (TypeF (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0]) Type0,cz) (Ret annz (Error annz 99)))
          (CallS annz
            (Call (annz {type_ = (Type0,cz)})
              (Read (annz {type_ = (TypeF (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0]) Type0,cz)}) "$fff$((A,A) -> ())$")
              (Tuple
                (annz {type_ = (TypeN [TypeD ["A"] [] Type0,TypeD ["A"] [] Type0],cz)}) [Cons (annz {type_ = (TypeD ["A"] [] Type0,cz)}) ["A"],Cons (annz {type_ = (TypeD ["A"] [] Type0,cz)}) ["A"]])))
          (Ret annz (Error annz 99))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0, cvc ("a","Xable")),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0, cvc ("a","Xable"))
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeD ["A"] [] Type0) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Cons annz ["Int","1"])))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (bool,cz) False
        (Class annz "Equalable" (cv "a") [(annz,"eq",(TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (bool),cz),False)]
        (Var annz "eq" (TypeF (TypeN [(TypeV "a"),(TypeV "a")]) (bool),cz)
        (CallS annz (Call annz (Read annz "eq") (Tuple annz [(Cons annz ["Bool"]),(Cons annz ["Int","1"])]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (bool,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (bool,cz)
          [(annz, "fff", (TypeF (bool) Type0,cz), True)]
          (func "$fff$(Bool -> ())$" (TypeF (bool) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (int,cz)
                [(annz, "fff", (TypeF (int) Type0,cz), True)]
                (func "$fff$(Int -> ())$" (TypeF (int) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (Seq annz
                      (CallS annz (Call annz (Read annz "fff") (Cons annz ["Int","1"])))
                      (CallS annz (Call annz (Read annz "fff") (Cons annz ["Bool"])))))))))))))))
      `shouldBe` [] --,Data annz ["Int"] [] [] Type0 False (Data annz ["Bool"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(Bool -> ())" (TypeF (TypeD ["Bool"]) Type0) (Var annz "fff$(Int -> ())" (TypeF (TypeD ["Int"]) Type0) (Seq annz (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["Int"]) Type0,[]}) "fff$(Int -> ())") (Cons (annz {type_ = (TypeD ["Int","1"],[]}) ["Int","1"]))) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["Bool"]) Type0,[]}) "fff$(Bool -> ())") (Cons (annz {type_ = (TypeD ["Bool"],[]}) ["Bool"] (Unit (annz {type_ = (Type0,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeD ["A"] [] Type0) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"])))))))))))
      `shouldBe` [] --,Data annz ["A"] [] [] Type0 False (Data annz ["A","B"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(A -> ())" (TypeF (TypeD ["A"]) Type0) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["A"]) Type0,[]}) "fff$(A -> ())") (Cons (annz {type_ = (TypeD ["A","B"],[]}) ["A","B"] (Unit (annz {type_ = (Type0,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"]     [] Type0,cz) False
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeD ["A"] [] Type0) Type0,cz), True)]
          (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A","B"] [] Type0,cz)
                [(annz, "fff", (TypeF (TypeD ["A","B"] [] Type0) Type0,cz), True)]
                (func "$fff$((A,B) -> ())$" (TypeF (TypeD ["A","B"] [] Type0) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"]))))))))))))))
      `shouldBe` [] --,Data annz ["A"] [] [] Type0 False (Data annz ["A","B"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" ["Xable"]) Type0) (Var annz "fff$(A -> ())" (TypeF (TypeD ["A"]) Type0) (Var annz "fff$(A.B -> ())" (TypeF (TypeD ["A","B"]) Type0) (CallS annz (Call (annz {type_ = (Type0,[]}) (Read (annz {type_ = (TypeF (TypeD ["A","B"]) Type0,[]}) "fff$(A.B -> ())") (Cons (annz {type_ = (TypeD ["A","B"],[]}) ["A","B"] (Unit (annz {type_ = (Type0,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["A"] [] Type0,cz) False
        (Data annz (TypeD ["A","B"] [] Type0,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TypeF (TypeV "a") Type0,cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") Type0,cz)
        (Inst annz "Xable" (TypeD ["A","B"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeD ["A","B"] [] Type0) Type0,cz), True)]
          (func "$fff$((A,B) -> ())$" (TypeF (TypeD ["A","B"] [] Type0) Type0,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TypeD ["A"] [] Type0,cz)
                [(annz, "fff", (TypeF (TypeD ["A"] [] Type0) Type0,cz), True)]
                (func "$fff$(A -> ())$" (TypeF (TypeD ["A"] [] Type0) Type0,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Cons annz ["A","B"]))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["B"] [] Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF Type0 (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF Type0 (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B"] [] Type0,cz)
          [(annz, "fff", (TypeF Type0 (TypeD ["B"] [] Type0),cz), True)]
          (func "$fff$(() -> B)$" (TypeF Type0 (TypeD ["B"] [] Type0),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] [] Type0 False (Var annz "fff" (TypeF Type0 (TypeV "b" ["X"])) (Var annz "fff$(() -> B)" (TypeF Type0 (TypeD ["B"])) (CallS annz (Call (annz {type_ = (TypeD ["B"],[]}) (Read (annz {type_ = (TypeF Type0 (TypeD ["B"]),[]}) "fff$(() -> B)") (Unit (annz {type_ = (Type0,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["B"] [] Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B"] [] Type0),cz), True)]
          (func "$fff$(a -> B)$" (TypeF (TypeV "a") (TypeD ["B"] [] Type0),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B)" (TypeF (TypeV "a" []) (TypeD ["B"])) (CallS annz (Call (annz {type_ = (TypeD ["B"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B"]),[]}) "fff$(a -> B)") (Unit (annz {type_ = (Type0,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["B1"] [] Type0,cz) False
        (Data annz (TypeD ["B2"] [] Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz), True)]
          (func "$fff$(a -> B)$" (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"] [] Type0,cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (Call annz (Read annz "fff") (Unit annz))))))))))))))
                  -- the problem is that CallS accept any return data
      `shouldBe` [] --,Data annz ["B1"] [] [] Type0 False (Data annz ["B2"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (CallS annz (Call (annz {type_ = (TypeD ["B2"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B2"]),[]}) "fff$(a -> B2)") (Unit (annz {type_ = (Type0,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["B1"] [] Type0,cz) False
        (Data annz (TypeD ["B2"] [] Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz), True)]
          (func "$fff$(a -> B1)$" (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"] [] Type0,cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b1" (TypeD ["B1"] [] Type0,cz)
                    (Match annz False (LVar "b1")
                      (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] [] Type0 False (Data annz ["B2"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b1" (TypeD ["B1"]) (Match annz False (LVar "b1") (Call (annz {type_ = (TypeD ["B1"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B1"]),[]}) "fff$(a -> B1)") (Unit (annz {type_ = (Type0,[]}))) (Nop annz) (Nop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (Data annz (TypeD ["B1"] [] Type0,cz) False
        (Data annz (TypeD ["B2"] [] Type0,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TypeF (TypeV "a") (TypeV "b"),cz),False)]
        (Var annz "fff" (TypeF (TypeV "a") (TypeV "b"),cz)
        (Inst annz "X" (TypeD ["B1"] [] Type0,cz)
          [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz), True)]
          (func "$fff$(a -> B1)$" (TypeF (TypeV "a") (TypeD ["B1"] [] Type0),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TypeD ["B2"] [] Type0,cz)
                [(annz, "fff", (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz), True)]
                (func "$fff$(a -> B2)$" (TypeF (TypeV "a") (TypeD ["B2"] [] Type0),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b2" (TypeD ["B2"] [] Type0,cz)
                    (Match annz False (LVar "b2")
                      (Call annz (Read annz "fff") (Unit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] [] Type0 False (Data annz ["B2"] [] [] Type0 False (Var annz "fff" (TypeF (TypeV "a" []) (TypeV "b" ["X"])) (Var annz "fff$(a -> B1)" (TypeF (TypeV "a" []) (TypeD ["B1"])) (Var annz "fff$(a -> B2)" (TypeF (TypeV "a" []) (TypeD ["B2"])) (Var annz "b2" (TypeD ["B2"]) (Match annz False (LVar "b2") (Call (annz {type_ = (TypeD ["B2"],[]}) (Read (annz {type_ = (TypeF (TypeV "a" []) (TypeD ["B2"]),[]}) "fff$(a -> B2)") (Unit (annz {type_ = (Type0,[]}))) (Nop annz) (Nop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
