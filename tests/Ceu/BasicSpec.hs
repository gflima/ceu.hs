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

int   = TData ["Int"]          [] TUnit
bool  = TData ["Bool"]         [] TUnit
boolf = TData ["Bool","False"] [] TUnit
boolt = TData ["Bool","True"]  [] TUnit

main :: IO ()
main = hspec spec

func id tp p = Var annz id tp
                (Match annz False (LVar id)
                  (EFunc annz tp (Ret annz (EError annz 99)))
                  p
                  (Ret annz (EError annz 99)))

spec :: Spec
spec = do

  --describe "TODO" $ do

  describe "declarations" $ do

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
            (CallS annz (ECall annz (EVar annz "==")
              (ETuple annz
                [EData annz ["Bool","True"],
                 EData annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (ECall annz (EVar annz "==")
              (ETuple annz
                [EData annz ["Bool","True"],
                 EData annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "x <- 0" $
      (fst $ TypeSys.go (Match annz False (LVar "x") (EData annz ["Int","0"]) (Nop annz) (Nop annz)))
        `shouldBe` ["variable 'x' is not declared","data 'Int.0' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

    checkCheckIt (Nop annz)                  []
    checkCheckIt (prelude annz (Var annz "a" (TTuple [int,int],cz) (Match annz False (LVar "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int'"]
    --checkCheckIt (Var annz "a" TUnit (Match annz False (LVar "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz))) ["types do not match"]
    checkCheckIt (prelude annz (Var annz "a" (TUnit,cz) (Match annz False (LVar "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz)))) ["types do not match : expected '()' : found 'Int'"]

    it "a <- 1" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (int,cz) (Match annz False (LVar "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` []

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (TUnit,cz) (Match annz True (LCons ["Bool","True"] LUnit) (EVar annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (int,cz) (Match annz True (LCons ["Bool","True"] LUnit) (EVar annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (bool,cz) (Match annz True (LCons ["Bool","True"] LUnit) (EVar annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (Var annz "a" (bool,cz) (Match annz False (LCons ["Bool","True"] LUnit) (EVar annz "a") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

    checkCheckIt (Var annz "a" (TUnit,cz) (Var annz "a" (TUnit,cz) (Nop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (prelude annz $ Match annz False (LVar "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (Var annz "umn" (TFunc (int) (int),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (Nop annz) (Nop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TFunc (int) (int),cz)
        (Var annz "a" (TUnit,cz)
        (Match annz False (LVar "a") (ECall annz (EVar annz "umn") (EData annz ["Int","1"])) (Nop annz) (Nop annz))))))
      `shouldBe` ["types do not match : expected '(Int -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (Var annz "umn" (TFunc (int) (int),cz)
        (Var annz "a" (TUnit,cz)
        (Match annz False (LVar "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (Nop annz) (Nop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (prelude annz $ Match annz False (LVar "a") (ECall annz (EVar annz "f") (EData annz ["Int","1"])) (Nop annz) (Nop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (Var annz "x" (TTuple [TUnit,TUnit],cz) (Match annz False (LVar "x") (EUnit annz) (Nop annz) (Nop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (Var annz "x" (int,cz) (Match annz False (LVar "x") (EUnit annz) (Nop annz) (Nop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (Var annz "identity" (TFunc (TAny "a") (TAny "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (ECall annz (EVar annz "identity") (EData annz ["Int","1"])) (Nop annz) (Nop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (TTop,cz)
        (Match annz False (LVar "ret") (EData annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (TTop,cz)
        (Match annz True (LVar "ret") (EData annz ["Int","1"]) (Nop annz) (Nop annz)))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TTop,cz)
        (Var annz "b" (TTop,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (ETuple annz [EData annz ["Int","1"],EData annz ["Int","2"]]) (Nop annz) (Nop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TTop,cz)
        (Var annz "b" (TTop,cz)
        (Match annz True (LTuple [LVar "a",LVar "b"]) (ETuple annz [EData annz ["Int","1"],EData annz ["Int","2"]]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never fails"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TTop,cz)
        (Var annz "b" (TTop,cz)
        (Match annz False (LTuple [LVar "a",LVar "b"]) (ETuple annz [EData annz ["Int","1"],EData annz ["Int","2"],EData annz ["Int","3"]]) (Nop annz) (Nop annz))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "a" (TTop,cz)
        (Var annz "b" (TTop,cz)
        (Var annz "c" (TTop,cz)
        (Match annz False (LTuple [LVar "a",LVar "b",LVar "c"]) (ETuple annz [EData annz ["Int","1"],EData annz ["Int","2"]]) (Nop annz) (Nop annz)))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "f" (TFunc TUnit (int),cz)
        (Var annz "ret" (TTop,cz)
        (Match annz False (LVar "ret") (ECall annz (EVar annz "f") (EUnit annz)) (Nop annz) (Nop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (int,cz)
        (Match annz True (LCons ["Int","1"] LUnit) (EVar annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "ret" (int,cz)
        (Match annz False (LCons ["Int","1"] LUnit) (EVar annz "ret") (Nop annz) (Nop annz)))))
        `shouldBe` ["match might fail"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (Var annz "f" (TFunc TUnit (int),cz) (Nop annz)))
        `shouldBe` ["data 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (Var annz "f" (TFunc TUnit TUnit,cz) (Var annz "f" (TFunc TUnit TUnit,cz) (Nop annz)))
        `shouldBe` ([],Var annz "f" (TFunc TUnit TUnit,cz) (Var annz "f" (TFunc TUnit TUnit,cz) (Nop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (Var annz "f" (TFunc (TAny "a") (TAny "a"),cz) (Var annz "f" (TFunc TUnit TUnit,cz) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TFunc (TAny "a") (TAny "a"),cz) (Var annz "f" (TFunc TUnit TUnit,cz) (Nop annz)))

    it "func f; func ~f" $
      TypeSys.go (Var annz "f" (TFunc TUnit TUnit,cz) (Var annz "f" (TFunc TUnit TTop,cz) (Nop annz)))
        `shouldBe` (["variable 'f' is already declared"],Var annz "f" (TFunc TUnit TUnit,cz) (Var annz "f" (TFunc TUnit TTop,cz) (Nop annz)))

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (Var annz "first" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (TAny "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (ECall annz (EVar annz "first") (ETuple annz [(EUnit annz),(EData annz ["Int","1"])])) (Nop annz) (Nop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambiguous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous instances for 'a' : '()', 'Int', 'Int'"]

{-
    checkCheckIt (prelude annz (Var annz "first" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (TAny "a"),cz) (Var annz "a" (int,cz) (Match annz False (LVar "a") (ECall annz (EVar annz "first") (ETuple annz [(EData annz ["Int","1"]),(EData annz ["Int","1"])])) (Nop annz) (Nop annz))))) []
-}

    it "() <- EArg" $
      (fst $ TypeSys.go
        (Match annz False LUnit (EArg annz) (Nop annz) (Nop annz)))
      `shouldBe` []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (Var annz "f" (TFunc TUnit TUnit,cz)
        (Match annz False (LVar "f")
          (EFunc annz (TFunc TUnit TUnit,cz)
            (Ret annz (EArg annz)))
          (Nop annz)
          (Nop annz))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (Var annz "f" (TFunc TUnit (TAny "a"),cz)
        (Ret annz (ECall annz (EVar annz "f") (EUnit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Var annz "f" (TFunc (TAny "a") (int),cz)
        (Ret annz (ECall annz (EVar annz "f") (EData annz ["Int","1"]))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (Data annz (int,cz) False
        (Class annz "X" (cv "a") [(annz,"fff",(TFunc (TAny "a") (int),cvc ("a","X")),False)]
            (Var annz "fff" (TFunc (TAny "a") (int),cvc ("a","X"))
        (Inst annz "X" (int,cz)
            [(annz,"fff",(TFunc (int) (int),cz),True)]
            (Var annz "fff" (TFunc (int) (int),cz)
            (Match annz False
              (LVar "fff")
              (EFunc annz (TFunc (int) (int),cz)
                (Ret annz (EData annz ["Int","1"])))
              (Seq annz
                (Nop annz)
                (Ret annz (ECall annz (EVar annz "fff") (EData annz ["Int","1"])))
              )
              (Nop annz))))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (prelude annz $ Match annz False (LCons ["Int","1"] LUnit) (EData annz ["Int","1"]) (Nop annz) (Nop annz))
      `shouldBe` ([],Data annz (TData ["Int"] [] TUnit,cz) False (Data annz (TData ["Bool"] [] TUnit,cz) False (Data annz (TData ["Bool","True"] [] TUnit,cz) False (Data annz (TData ["Bool","False"] [] TUnit,cz) False (Match annz{type_=(TBot,cz)} False (LCons ["Int","1"] LUnit) (EData annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (Nop annz) (Nop annz))))))
    it "1 <- 2" $
      TypeSys.go (prelude annz $ Match annz True (LCons ["Int","1"] LUnit) (EData annz ["Int","2"]) (Nop annz) (Nop annz))
      `shouldBe` (["match never succeeds : data mismatch"],Data annz (TData ["Int"] [] TUnit,cz) False (Data annz (TData ["Bool"] [] TUnit,cz) False (Data annz (TData ["Bool","True"] [] TUnit,cz) False (Data annz (TData ["Bool","False"] [] TUnit,cz) False (Match annz True (LCons ["Int","1"] LUnit) (EData (annz {type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","2"]) (Nop annz) (Nop annz))))))
    it "_ = 1" $
      TypeSys.go (Match annz False LAny (EData annz ["Int","1"]) (Nop annz) (Nop annz))
      `shouldBe` (["data 'Int.1' is not declared"],Match annz{type_=(TBot,cz)} False LAny (EData annz{type_=(TAny "?",cz)} ["Int","1"]) (Nop annz) (Nop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Match annz False (LTuple [LVar "x", LAny]) (EData annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` (["match never succeeds"],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz{type_=(TBot,cz)} "x" (int,cz) (Match annz{type_=(TBot,cz)} False (LTuple [LVar "x",LAny]) (EData annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Match annz False (LTuple [LVar "x", LAny]) (ETuple annz [EData annz ["Int","1"], EData annz ["Int","1"]]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var (annz{type_ = (TBot,cz)}) "x" (int,cz) (Match (annz{type_ = (TBot,cz)}) False (LTuple [LVar "x",LAny]) (ETuple (annz{type_ = (TTuple [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit],cz)}) [EData (annz{type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","1"],EData (annz{type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","1"]]) (Nop annz) (Nop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (Var annz "x" (int,cz)
              (Var annz "y" (TTuple [TUnit, int],cz)
                (Match annz False
                  (LTuple [LTuple [LAny,LVar "x"], LAny])
                  (ETuple annz [EVar annz "y", EData annz ["Int","1"]])
                  (Nop annz)
                  (Nop annz)))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var (annz{type_ = (TBot,cz)}) "x" (int,cz) (Var (annz{type_ = (TBot,cz)}) "y" (TTuple [TUnit,int],cz) (Match (annz{type_ = (TBot,cz)}) False (LTuple [LTuple [LAny,LVar "x"],LAny]) (ETuple (annz{type_ = (TTuple [TTuple [TUnit,int],TData ["Int"] [] TUnit],cz)}) [EVar (annz{type_ = (TTuple [TUnit,int],cz)}) "y",EData annz{type_ = (TData ["Int"] [] TUnit,cz)} ["Int","1"]]) (Nop annz) (Nop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (int,cz) (Match annz True (LExp $ EVar annz "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz "a" (int,cz) (Match annz True (LExp $ EVar annz{type_ = (int,cz)} "a") (EData annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (Var annz "a" (TUnit,cz) (Match annz True (LExp $ EVar annz "a") (EData annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],Data annz (int,cz) False (Data annz (bool,cz) False (Data annz (boolt,cz) False (Data annz (boolf,cz) False (Var annz "a" (TUnit,cz) (Match annz True (LExp $ EVar annz{type_ = (TUnit,cz)} "a") (EData annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (Nop annz) (Nop annz)))))))

    it "data X with Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (Data annz (TData ["Xxx"] [] int,cz) False (Match annz True (LCons ["Xxx"] (LCons ["Int","1"] LUnit)) (ECall annz (EData annz ["Xxx"]) (EData annz ["Int","2"])) (Ret annz (EData annz ["Int","2"])) (Nop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (Match annz True (LCons ["A"] LUnit) (EData annz ["Int","1"]) (Nop annz) (Nop annz)))
      `shouldBe` ["data 'A' is not declared","match never succeeds : data mismatch"] --"types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) True
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Match annz False (LCons ["A"] LAny) (EData annz ["A","B"]) (Nop annz) (Nop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"]     [] TUnit,cz) True
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Var  annz "x" (TData ["A","B"] [] TUnit,cz)
        (Match annz False (LCons ["A"] LAny) (EData annz ["A","B"]) (Nop annz) (Nop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"]     [] TUnit,cz) False
        (Data annz (TData ["A","B"] [] TUnit,cz) True
        (Match annz True (LCons ["A","B"] LAny) (EData annz ["A"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (Data annz (TData ["A"] [] TUnit,cz) True (Match annz True (LCons ["A"] LUnit) (EData annz ["Int","1"]) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds : data mismatch"] --["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (Data annz (TData ["A"] [] TUnit,cz) False (Match annz False (LCons ["A"] LUnit) (ECall annz (EData annz ["A"]) (EData annz ["Int","1"])) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (prelude annz $ Data annz (TData ["A"] [] TUnit,cz) False (Match annz False (LCons ["A"] (LCons ["Int","1"] LUnit)) (EData annz ["A"]) (Nop annz) (Nop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["A"] [] TUnit,cz) True
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Var  annz "x" (TTuple [int, TData ["A","B"] [] TUnit],cz)
        (Match annz True (LTuple [LCons ["Int","1"] LUnit, LCons ["A"] LUnit]) (EVar annz "x") (Nop annz) (Nop annz)))))))
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
        (Data annz (TData ["Bool","True","Xxx"] [] TUnit,cz) False (Nop annz)))
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
            (Match annz False (LVar "x") (EData annz ["Bool"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
          (Var annz "x" (bool,cz)
            (Match annz False (LVar "x") (EData annz ["Bool","True"]) (Nop annz) (Nop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
            (CallS annz (ECall annz (EVar annz "==")
              (ETuple annz
                [EData annz ["Bool","True"],
                 EData annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (ECall annz (EVar annz "==")
              (ETuple annz
                [EData annz ["Bool","True"],
                 EData annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` []

    it "Int ; Bool.* ; True <- True==False" $
      (fst $ TypeSys.go
        (Data annz (int,cz) True
        (Data annz (bool,cz) True
        (Data annz (boolt,cz) False
        (Data annz (boolf,cz) False
        (Var annz "==" (TFunc (TTuple [(int),(int)]) (bool),cz)
          (Match annz True
            (LCons ["Bool","True"] LUnit)
            (ECall annz (EVar annz "==")
              (ETuple annz
                [EData annz ["Bool","True"],
                 EData annz ["Bool","False"]]))
            (Nop annz)
            (Nop annz))))))))
      `shouldBe`
        ["types do not match : expected '((Bool.True,Bool.False) -> Bool)' : found '((Int,Int) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (Var annz "x" (bool,cz)
          (Match annz False (LVar "x") (EData annz{type_=(bool,cz)} ["Bool","True"]) (Nop annz) (Nop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (Data annz (TData ["X"] [] int,cz) False
        (Var annz "x" (TData ["X"] [] TUnit,cz)
          (Match annz False (LVar "x") (EData annz ["X"]) (Nop annz) (Nop annz)))))
      `shouldBe` ["types do not match : expected 'X' : found '(Int -> X)'"]
      --["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (Data annz (TData ["X"] [] int,cz) False
        (Var annz "x" (TData ["X"] [] (int),cz)
          (Match annz False (LVar "x") (ECall annz (EData annz ["X"]) (EData annz ["Int","1"])) (Nop annz) (Nop annz)))))
      `shouldBe` ["data 'Int' is not declared","data 'Int.1' is not declared"]

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["X"]     [] int,cz) False
        (Data annz (TData ["X","Y"] [] int,cz) False
        (Nop annz)))))
      `shouldBe` ([],Data annz (int,cz) False (Data annz (TData ["X"] [] int,cz) False (Data annz (TData ["X","Y"] [] int,cz) False (Nop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["X"] [] (TTuple [int, int]),cz) False
        (Var annz "x" (TData ["X"] [] (TTuple [int, int]),cz)
          (Match annz False (LVar "x") (ECall annz (EData annz ["X"]) (ETuple annz [EData annz ["Int","1"], EData annz ["Int","2"]])) (Nop annz) (Nop annz))))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (Data annz (int,cz) False
          (Data annz (TData ["X"] [] int,cz) False
          (Var annz "x" (int,cz)
          (Match annz False (LCons ["X"] (LVar "x")) (ECall annz (EData annz ["X"]) (EData annz ["Int","1"])) (Nop annz) (Nop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (Data annz (int,cz) False
          (Data annz (TData ["X"] [] int,cz) False
          (Var annz "x" (int,cz)
          (Match annz False (LCons ["X"] (LVar "x")) (EData annz ["X"]) (Nop annz) (Nop annz))))))
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
        (Var annz "f" (TFunc (TAny "a") TUnit,cvc ("a","X"))
        (Class annz "Y" (cv "a") []
        (Var annz "f" (TFunc (TAny "a") TUnit,cvc ("a","Y"))
        (Nop annz))))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (Class annz "X" (cv "a") []
        (Var annz "f" (TFunc (TAny "a") TUnit, cvc ("a","X"))
        (Var annz "f" (TFunc (TAny "a") TUnit,cz)
        (Nop annz)))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (Nop annz)))
      `shouldBe` (["data 'Bool' is not declared"],(Var annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz (bool,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (Nop annz))))
      `shouldBe` ([],Data annz (bool,cz) True (Var annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz) (Nop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (Data annz (bool,cz) True
        (Class annz "Equalable" (cv "a") []
        (Var annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool), cvc ("a","Equalable"))
        (Nop annz))))
      `shouldBe` ([],Data annz (bool,cz) True (Nop annz))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
                [(annz,"fff",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
                (Var annz "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
                (Seq annz
                  (Nop annz)
                  (Nop annz))))
            )))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff2",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
          (func "fff2" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Nop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz) []
          (Seq annz
            (Nop annz)
            (Nop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (TData ["A"] [] TUnit) (int),cz),True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) (int),cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "X" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (int) TUnit,cz),True)]
          (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
          (Var annz "fff" (TFunc (TAny "a") TUnit,cz)        -- a
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)                          -- A
          [(annz, "fff", (TFunc (int) TUnit,cz), True)]
          (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)  -- Int
            (Seq annz
              (Nop annz)
              (Nop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (ECall annz (EVar annz "fff") (EData annz ["A"]))))))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; Inst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit, cvc ("a","Xable"))
        (Inst annz "Xable" (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit],cz)
          [(annz, "fff", (TFunc (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit]) TUnit,cz), True)]
          (func "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit]) TUnit,cz)
            (CallS annz (ECall annz (EVar annz "fff") (ETuple annz [(EData annz ["A"]),(EData annz ["A"])]))))))))
      `shouldBe` ([],
        Data annz (TData ["A"] [] TUnit,cz) False
        (Var annz "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)
        (Var annz "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)
        (Match annz False (LVar "$fff$((A,A) -> ())$")
          (EFunc (annz {type_ = (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)}) (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz) (Ret annz (EError annz 99)))
          (CallS annz
            (ECall (annz {type_ = (TUnit,cz)})
              (EVar (annz {type_ = (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)}) "$fff$((A,A) -> ())$")
              (ETuple
                (annz {type_ = (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit],cz)}) [EData (annz {type_ = (TData ["A"] [] TUnit,cz)}) ["A"],EData (annz {type_ = (TData ["A"] [] TUnit,cz)}) ["A"]])))
          (Ret annz (EError annz 99))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit, cvc ("a","Xable")),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit, cvc ("a","Xable"))
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (ECall annz (EVar annz "fff") (EData annz ["Int","1"])))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (bool,cz) False
        (Class annz "Equalable" (cv "a") [(annz,"eq",(TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz),False)]
        (Var annz "eq" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (CallS annz (ECall annz (EVar annz "eq") (ETuple annz [(EData annz ["Bool"]),(EData annz ["Int","1"])]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (Data annz (int,cz) False
        (Data annz (bool,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (bool,cz)
          [(annz, "fff", (TFunc (bool) TUnit,cz), True)]
          (func "$fff$(Bool -> ())$" (TFunc (bool) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (int,cz)
                [(annz, "fff", (TFunc (int) TUnit,cz), True)]
                (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)
                  (Seq annz
                    (Nop annz)
                    (Seq annz
                      (CallS annz (ECall annz (EVar annz "fff") (EData annz ["Int","1"])))
                      (CallS annz (ECall annz (EVar annz "fff") (EData annz ["Bool"])))))))))))))))
      `shouldBe` [] --,Data annz ["Int"] [] [] TUnit False (Data annz ["Bool"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (Var annz "fff$(Bool -> ())" (TFunc (TData ["Bool"]) TUnit) (Var annz "fff$(Int -> ())" (TFunc (TData ["Int"]) TUnit) (Seq annz (CallS annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["Int"]) TUnit,[]}) "fff$(Int -> ())") (EData (annz {type_ = (TData ["Int","1"],[]}) ["Int","1"]))) (CallS annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["Bool"]) TUnit,[]}) "fff$(Bool -> ())") (EData (annz {type_ = (TData ["Bool"],[]}) ["Bool"] (EUnit (annz {type_ = (TUnit,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (CallS annz (ECall annz (EVar annz "fff") (EData annz ["A","B"])))))))))))
      `shouldBe` [] --,Data annz ["A"] [] [] TUnit False (Data annz ["A","B"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (Var annz "fff$(A -> ())" (TFunc (TData ["A"]) TUnit) (CallS annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["A"]) TUnit,[]}) "fff$(A -> ())") (EData (annz {type_ = (TData ["A","B"],[]}) ["A","B"] (EUnit (annz {type_ = (TUnit,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"]     [] TUnit,cz) False
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TData ["A","B"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TData ["A","B"] [] TUnit) TUnit,cz), True)]
                (func "$fff$((A,B) -> ())$" (TFunc (TData ["A","B"] [] TUnit) TUnit,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (ECall annz (EVar annz "fff") (EData annz ["A","B"]))))))))))))))
      `shouldBe` [] --,Data annz ["A"] [] [] TUnit False (Data annz ["A","B"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (Var annz "fff$(A -> ())" (TFunc (TData ["A"]) TUnit) (Var annz "fff$(A.B -> ())" (TFunc (TData ["A","B"]) TUnit) (CallS annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["A","B"]) TUnit,[]}) "fff$(A.B -> ())") (EData (annz {type_ = (TData ["A","B"],[]}) ["A","B"] (EUnit (annz {type_ = (TUnit,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (Data annz (TData ["A"] [] TUnit,cz) False
        (Data annz (TData ["A","B"] [] TUnit,cz) False
        (Class annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (Var annz "fff" (TFunc (TAny "a") TUnit,cz)
        (Inst annz "Xable" (TData ["A","B"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A","B"] [] TUnit) TUnit,cz), True)]
          (func "$fff$((A,B) -> ())$" (TFunc (TData ["A","B"] [] TUnit) TUnit,cz)
            (Seq annz
              (Nop annz)
              (Inst annz "Xable" (TData ["A"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
                (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (ECall annz (EVar annz "fff") (EData annz ["A","B"]))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (Data annz (TData ["B"] [] TUnit,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TFunc TUnit (TAny "b"),cz),False)]
        (Var annz "fff" (TFunc TUnit (TAny "b"),cz)
        (Inst annz "X" (TData ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc TUnit (TData ["B"] [] TUnit),cz), True)]
          (func "$fff$(() -> B)$" (TFunc TUnit (TData ["B"] [] TUnit),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] [] TUnit False (Var annz "fff" (TFunc TUnit (TAny "b" ["X"])) (Var annz "fff$(() -> B)" (TFunc TUnit (TData ["B"])) (CallS annz (ECall (annz {type_ = (TData ["B"],[]}) (EVar (annz {type_ = (TFunc TUnit (TData ["B"]),[]}) "fff$(() -> B)") (EUnit (annz {type_ = (TUnit,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (Data annz (TData ["B"] [] TUnit,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (Var annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (Inst annz "X" (TData ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc (TAny "a") (TData ["B"] [] TUnit),cz)
            (Seq annz
              (Nop annz)
              (CallS annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,Data annz ["B"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (Var annz "fff$(a -> B)" (TFunc (TAny "a" []) (TData ["B"])) (CallS annz (ECall (annz {type_ = (TData ["B"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B"]),[]}) "fff$(a -> B)") (EUnit (annz {type_ = (TUnit,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (Data annz (TData ["B1"] [] TUnit,cz) False
        (Data annz (TData ["B2"] [] TUnit,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (Var annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (Inst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (Seq annz
                    (Nop annz)
                    (CallS annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))))))
                  -- the problem is that CallS accept any return data
      `shouldBe` [] --,Data annz ["B1"] [] [] TUnit False (Data annz ["B2"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (Var annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (Var annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (CallS annz (ECall (annz {type_ = (TData ["B2"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {type_ = (TUnit,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (Data annz (TData ["B1"] [] TUnit,cz) False
        (Data annz (TData ["B2"] [] TUnit,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (Var annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (Inst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b1" (TData ["B1"] [] TUnit,cz)
                    (Match annz False (LVar "b1")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] [] TUnit False (Data annz ["B2"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (Var annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (Var annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (Var annz "b1" (TData ["B1"]) (Match annz False (LVar "b1") (ECall (annz {type_ = (TData ["B1"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B1"]),[]}) "fff$(a -> B1)") (EUnit (annz {type_ = (TUnit,[]}))) (Nop annz) (Nop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (Data annz (TData ["B1"] [] TUnit,cz) False
        (Data annz (TData ["B2"] [] TUnit,cz) False
        (Class annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (Var annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (Inst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (Seq annz
              (Nop annz)
              (Inst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (Seq annz
                    (Nop annz)
                    (Var annz "b2" (TData ["B2"] [] TUnit,cz)
                    (Match annz False (LVar "b2")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (Nop annz) (Nop annz))))))))))))))
      `shouldBe` [] --,Data annz ["B1"] [] [] TUnit False (Data annz ["B2"] [] [] TUnit False (Var annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (Var annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (Var annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (Var annz "b2" (TData ["B2"]) (Match annz False (LVar "b2") (ECall (annz {type_ = (TData ["B2"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {type_ = (TUnit,[]}))) (Nop annz) (Nop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
