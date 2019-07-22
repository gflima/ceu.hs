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

mmm :: Ann -> Bool -> Exp -> Exp -> Stmt -> Stmt -> Stmt
mmm z b pat exp p1 p2 = SMatch z b exp [(SNop z,pat,p1)]

mmm' :: Ann -> Bool -> Exp -> Exp -> Stmt -> Stmt -> Stmt
mmm' z b pat exp p1 p2 = SMatch z b exp [(SNop z,pat,p1),(SNop z,EAny z, SRet z $ EError z (-2))]

func id tp p = SVar annz id tp
                (mmm annz False (EVar annz id)
                  (EFunc annz FuncGlobal tp (SRet annz (EError annz 99)))
                  p
                  (SRet annz (EError annz 99)))

spec :: Spec
spec = do

  --describe "TODO" $ do

  describe "declarations" $ do

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
            (SCall annz (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
          (mmm annz True
            (ECons annz ["Bool","True"])
            (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` []

    it "Bool ; True <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) False
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "x" (bool,cz)
          (mmm annz False
            (ECons annz ["Bool","True"])
            (EVar  annz "x")
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["match is non exhaustive"]

    it "Bool ; True <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) False
        (SData annz Nothing (boolt,cz) False
        (SVar annz "x" (bool,cz)
          (mmm annz False
            (ECons annz ["Bool","True"])
            (EVar  annz "x")
            (SNop annz)
            (SNop annz))))))
      `shouldBe` ["match is non exhaustive"]

    it "Bool ; True <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz)  True
        (SData annz Nothing (boolt,cz) False
        (SVar annz "x" (bool,cz)
          (mmm annz False
            (ECons annz ["Bool","True"])
            (EVar  annz "x")
            (SNop annz)
            (SNop annz))))))
      `shouldBe` []

    it "x <- 0" $
      (fst $ TypeSys.go (mmm annz False (EVar annz "x") (ECons annz ["Int","0"]) (SNop annz) (SNop annz)))
        `shouldBe` ["variable 'x' is not declared","data 'Int.0' is not declared"]

  --------------------------------------------------------------------------

  describe "checkTypeSys -- declarations" $ do

    checkCheckIt (SNop annz)                  []
    checkCheckIt (prelude annz (SVar annz "a" (TTuple [int,int],cz) (mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))) ["types do not match : expected '(Int,Int)' : found 'Int'"]
    --checkCheckIt (SVar annz "a" TUnit (mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))) ["types do not match"]
    checkCheckIt (prelude annz (SVar annz "a" (TUnit,cz) (mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))) ["types do not match : expected '()' : found 'Int'"]

    it "a <- 1" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` []

    it "a:() ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (TUnit,cz) (mmm annz True (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found '()'"]
    it "a:Int ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (int,cz) (mmm annz True (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` ["types do not match : expected 'Bool' : found 'Int'"]

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (bool,cz) (mmm annz True (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (bool,cz) (mmm annz False (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` ["match is non exhaustive"]

    checkCheckIt (SVar annz "a" (TUnit,cz) (SVar annz "a" (TUnit,cz) (SNop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (prelude annz $ mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (SVar annz "umn" (TFunc (int) (int),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (SNop annz) (SNop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (SVar annz "umn" (TFunc (int) (int),cz)
        (SVar annz "a" (TUnit,cz)
        (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
      `shouldBe` ["types do not match : expected '(Int -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (SVar annz "umn" (TFunc (int) (int),cz)
        (SVar annz "a" (TUnit,cz)
        (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (SNop annz) (SNop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (prelude annz $ mmm annz False (EVar annz "a") (ECall annz (EVar annz "f") (ECons annz ["Int","1"])) (SNop annz) (SNop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (SVar annz "x" (TTuple [TUnit,TUnit],cz) (mmm annz False (EVar annz "x") (EUnit annz) (SNop annz) (SNop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (SVar annz "x" (int,cz) (mmm annz False (EVar annz "x") (EUnit annz) (SNop annz) (SNop annz)))) ["types do not match : expected 'Int' : found '()'"]
  checkCheckIt (prelude annz (SVar annz "identity" (TFunc (TAny "a") (TAny "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "identity") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (TTop,cz)
        (mmm annz False (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (TTop,cz)
        (mmm annz True (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TTop,cz)
        (SVar annz "b" (TTop,cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TTop,cz)
        (SVar annz "b" (TTop,cz)
        (mmm annz True (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TTop,cz)
        (SVar annz "b" (TTop,cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"],ECons annz ["Int","3"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TTop,cz)
        (SVar annz "b" (TTop,cz)
        (SVar annz "c" (TTop,cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b",EVar annz "c"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz)))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "f" (TFunc TUnit (int),cz)
        (SVar annz "ret" (TTop,cz)
        (mmm annz False (EVar annz "ret") (ECall annz (EVar annz "f") (EUnit annz)) (SNop annz) (SNop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (int,cz)
        (mmm annz True (ECons annz ["Int","1"]) (EVar annz "ret") (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (int,cz)
        (mmm annz False (ECons annz ["Int","1"]) (EVar annz "ret") (SNop annz) (SNop annz)))))
        `shouldBe` ["match is non exhaustive"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (SVar annz "f" (TFunc TUnit (int),cz) (SNop annz)))
        `shouldBe` ["data 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (SVar annz "f" (TFunc TUnit TUnit,cz) (SVar annz "f" (TFunc TUnit TUnit,cz) (SNop annz)))
        `shouldBe` ([],SVar annz "f" (TFunc TUnit TUnit,cz) (SVar annz "f" (TFunc TUnit TUnit,cz) (SNop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (SVar annz "f" (TFunc (TAny "a") (TAny "a"),cz) (SVar annz "f" (TFunc TUnit TUnit,cz) (SNop annz)))
        `shouldBe` (["variable 'f' is already declared"],SVar annz "f" (TFunc (TAny "a") (TAny "a"),cz) (SVar annz "f" (TFunc TUnit TUnit,cz) (SNop annz)))

    it "func f; func ~f" $
      TypeSys.go (SVar annz "f" (TFunc TUnit TUnit,cz) (SVar annz "f" (TFunc TUnit TTop,cz) (SNop annz)))
        `shouldBe` (["variable 'f' is already declared"],SVar annz "f" (TFunc TUnit TUnit,cz) (SVar annz "f" (TFunc TUnit TTop,cz) (SNop annz)))

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (SVar annz "first" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (TAny "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "first") (ETuple annz [(EUnit annz),(ECons annz ["Int","1"])])) (SNop annz) (SNop annz))))))
        `shouldBe`
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambiguous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous instances for 'a' : '()', 'Int', 'Int'"]

{-
    checkCheckIt (prelude annz (SVar annz "first" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (TAny "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "first") (ETuple annz [(ECons annz ["Int","1"]),(ECons annz ["Int","1"])])) (SNop annz) (SNop annz))))) []
-}

    it "() <- EArg" $
      (fst $ TypeSys.go
        (mmm annz False (EUnit annz) (EArg annz) (SNop annz) (SNop annz)))
      `shouldBe` []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (SVar annz "f" (TFunc TUnit TUnit,cz)
        (mmm annz False (EVar annz "f")
          (EFunc annz FuncGlobal (TFunc TUnit TUnit,cz)
            (SRet annz (EArg annz)))
          (SNop annz)
          (SNop annz))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (SVar annz "f" (TFunc TUnit (TAny "a"),cz)
        (SRet annz (ECall annz (EVar annz "f") (EUnit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "f" (TFunc (TAny "a") (int),cz)
        (SRet annz (ECall annz (EVar annz "f") (ECons annz ["Int","1"]))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (SData annz Nothing (int,cz) False
        (SClass annz "X" (cv "a") [(annz,"fff",(TFunc (TAny "a") (int),cvc ("a","X")),False)]
            (SVar annz "fff" (TFunc (TAny "a") (int),cvc ("a","X"))
        (SInst annz "X" (int,cz)
            [(annz,"fff",(TFunc (int) (int),cz),True)]
            (SVar annz "fff" (TFunc (int) (int),cz)
            (mmm annz False
              (EVar annz "fff")
              (EFunc annz FuncGlobal (TFunc (int) (int),cz)
                (SRet annz (ECons annz ["Int","1"])))
              (SSeq annz
                (SNop annz)
                (SRet annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))
              )
              (SNop annz))))))))
      `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (prelude annz $ mmm annz False (ECons annz ["Int","1"]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))
      `shouldBe` ([],SData annz Nothing (TData ["Int"] [] TUnit,cz) False (SData annz Nothing (TData ["Bool"] [] TUnit,cz) True (SData annz Nothing (TData ["Bool","True"] [] TUnit,cz) False (SData annz Nothing (TData ["Bool","False"] [] TUnit,cz) False (mmm annz{type_=(TBot,cz)} False (ECons annz{type_ = (TData ["Int"] [] TUnit,cz)} ["Int","1"]) (ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz))))))
    it "1 <- 2" $
      TypeSys.go (prelude annz $ mmm annz True (ECons annz ["Int","1"]) (ECons annz ["Int","2"]) (SNop annz) (SNop annz))
      `shouldBe` (["match never succeeds : data mismatch"],SData annz Nothing (TData ["Int"] [] TUnit,cz) False (SData annz Nothing (TData ["Bool"] [] TUnit,cz) True (SData annz Nothing (TData ["Bool","True"] [] TUnit,cz) False (SData annz Nothing (TData ["Bool","False"] [] TUnit,cz) False (mmm' annz True (ECons annz{type_ = (TData ["Int"] [] TUnit,cz)} ["Int","1"]) (ECons (annz {type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","2"]) (SNop annz) (SNop annz))))))
    it "_ = 1" $
      TypeSys.go (mmm annz False (EAny annz) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))
      `shouldBe` (["data 'Int.1' is not declared"],mmm annz{type_=(TBot,cz)} False (EAny annz) (ECons annz{type_=(TAny "?",cz)} ["Int","1"]) (SNop annz) (SNop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["match never succeeds"],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz{type_=(TBot,cz)} "x" (int,cz) (mmm annz{type_=(TBot,cz)} False (ETuple annz [EVar annz "x",(EAny annz)]) (ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","1"]]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar (annz{type_ = (TBot,cz)}) "x" (int,cz) (mmm (annz{type_ = (TBot,cz)}) False (ETuple annz [EVar annz "x",(EAny annz)]) (ETuple (annz{type_ = (TTuple [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit],cz)}) [ECons (annz{type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","1"],ECons (annz{type_ = (TData ["Int"] [] TUnit,cz)}) ["Int","1"]]) (SNop annz) (SNop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (SVar annz "y" (TTuple [TUnit, int],cz)
                (mmm annz False
                  (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"], (EAny annz)])
                  (ETuple annz [EVar annz "y", ECons annz ["Int","1"]])
                  (SNop annz)
                  (SNop annz)))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar (annz{type_ = (TBot,cz)}) "x" (int,cz) (SVar (annz{type_ = (TBot,cz)}) "y" (TTuple [TUnit,int],cz) (mmm (annz{type_ = (TBot,cz)}) False (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"],(EAny annz)]) (ETuple (annz{type_ = (TTuple [TTuple [TUnit,int],TData ["Int"] [] TUnit],cz)}) [EVar (annz{type_ = (TTuple [TUnit,int],cz)}) "y",ECons annz{type_ = (TData ["Int"] [] TUnit,cz)} ["Int","1"]]) (SNop annz) (SNop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (int,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz "a" (int,cz) (mmm' annz True (EExp annz $ EVar annz{type_ = (TBot,cz)} "a") (ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (TUnit,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz "a" (TUnit,cz) (mmm' annz True (EExp annz $ EVar annz{type_ = (TBot,cz)} "a") (ECons annz{type_=(TData ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "data X with Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (SData annz Nothing (TData ["Xxx"] [] int,cz) False (mmm annz True (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"])) (SRet annz (ECons annz ["Int","2"])) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (mmm annz True (ECons annz ["A"])  (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` ["data 'A' is not declared","match never succeeds : data mismatch"] --"types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz)     True
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"]     [] TUnit,cz) True
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (SVar  annz "x" (TData ["A","B"] [] TUnit,cz)
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"]     [] TUnit,cz) False
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) True
        (mmm annz True (ECons annz ["A","B"]) (ECons annz ["A"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (prelude annz $ SData annz Nothing (TData ["A"] [] TUnit,cz) True (mmm annz True (ECons annz ["A"]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds : data mismatch"] --["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (SData annz Nothing (TData ["A"] [] TUnit,cz) False (mmm annz False (ECall annz (ECons annz ["A"]) (EUnit annz)) (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (prelude annz $ SData annz Nothing (TData ["A"] [] TUnit,cz) False (mmm annz False (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (ECons annz ["A"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["A"] [] TUnit,cz) True
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (SVar  annz "x" (TTuple [int, TData ["A","B"] [] TUnit],cz)
        (mmm annz True (ETuple annz [ECons annz ["Int","1"], ECons annz ["A"]]) (EVar annz "x") (SNop annz) (SNop annz)))))))
      `shouldBe` []

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SData annz Nothing (int,cz) False
        (SNop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolf,cz) False
        (SNop annz)))))
      `shouldBe` ["data 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["Bool","True","Xxx"] [] TUnit,cz) False (SNop annz)))
      `shouldBe` ["data 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (int,cz) False
        (SNop annz))))
      `shouldBe` ["data 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (SVar annz "x" (int,cz) (SNop annz)))
      `shouldBe` ["data 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
          (SVar annz "x" (bool,cz)
            (mmm annz False (EVar annz "x") (ECons annz ["Bool"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
          (SVar annz "x" (bool,cz)
            (mmm annz False (EVar annz "x") (ECons annz ["Bool","True"]) (SNop annz) (SNop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
            (SCall annz (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc (TTuple [(bool),(bool)]) (bool),cz)
          (mmm annz True
            (ECons annz ["Bool","True"])
            (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` []

    it "Int ; Bool.* ; True <- True==False" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) True
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc (TTuple [(int),(int)]) (bool),cz)
          (mmm annz True
            (ECons annz ["Bool","True"])
            (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))
            (SNop annz)
            (SNop annz))))))))
      `shouldBe`
        ["types do not match : expected '((Bool.True,Bool.False) -> Bool)' : found '((Int,Int) -> Bool)'"]

    it "~Bool ; x=True" $
      (fst $ TypeSys.go
        (SVar annz "x" (bool,cz)
          (mmm annz False (EVar annz "x") (ECons annz{type_=(bool,cz)} ["Bool","True"]) (SNop annz) (SNop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["X"] [] int,cz) False
        (SVar annz "x" (TData ["X"] [] TUnit,cz)
          (mmm annz False (EVar annz "x") (ECons annz ["X"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","types do not match : expected 'X' : found '(Int -> X)'"]
      --["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["X"] [] int,cz) False
        (SVar annz "x" (TData ["X"] [] (int),cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","data 'Int' is not declared","data 'Int.1' is not declared"]

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["X"]     [] int,cz) True
        (SData annz Nothing (TData ["X","Y"] [] int,cz) False
        (SNop annz)))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (TData ["X"] [] int,cz) True (SData annz Nothing (TData ["X","Y"] [] int,cz) False (SNop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["X"] [] (TTuple [int, int]),cz) False
        (SVar annz "x" (TData ["X"] [] (TTuple [int, int]),cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","2"]])) (SNop annz) (SNop annz))))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (SData annz Nothing (int,cz) False
          (SData annz Nothing (TData ["X"] [] int,cz) False
          (SVar annz "x" (int,cz)
          (mmm annz False (ECall annz (ECons annz ["X"]) (EVar annz "x")) (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (SData annz Nothing (int,cz) False
          (SData annz Nothing (TData ["X"] [] int,cz) False
          (SVar annz "x" (int,cz)
          (mmm annz False (ECall annz (ECons annz ["X"]) (EVar annz "x")) (ECons annz ["X"]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match never succeeds"]
          --["types do not match : expected 'X' : found '(Int -> X)'"]
          --["types do not match : expected 'Int' : found '()'"]

  --------------------------------------------------------------------------

  describe "typeclass:" $ do
    it "X.f ; X.f" $
      (fst $ TypeSys.go
        (SClass annz "X" (cv "a") []
        (SClass annz "X" (cv "a") []
        (SNop annz))))
      `shouldBe` ["constraint 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst $ TypeSys.go
        (SClass annz "X" (cv "a") []
        (SVar annz "f" (TFunc (TAny "a") TUnit,cvc ("a","X"))
        (SClass annz "Y" (cv "a") []
        (SVar annz "f" (TFunc (TAny "a") TUnit,cvc ("a","Y"))
        (SNop annz))))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (SClass annz "X" (cv "a") []
        (SVar annz "f" (TFunc (TAny "a") TUnit, cvc ("a","X"))
        (SVar annz "f" (TFunc (TAny "a") TUnit,cz)
        (SNop annz)))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (SNop annz)))
      `shouldBe` (["data 'Bool' is not declared"],(SVar annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz) (SNop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (SNop annz))))
      `shouldBe` ([],SData annz Nothing (bool,cz) True (SVar annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz) (SNop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool), cvc ("a","Equalable"))
        (SNop annz))))
      `shouldBe` ([],SData annz Nothing (bool,cz) True (SNop annz))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
                [(annz,"fff",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
                (SVar annz "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
                (SSeq annz
                  (SNop annz)
                  (SNop annz))))
            )))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz) []
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff2",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
          (func "fff2" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz) []
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (TData ["A"] [] TUnit) (int),cz),True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) (int),cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "X" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (int) TUnit,cz),True)]
          (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
          (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)        -- a
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)                          -- A
          [(annz, "fff", (TFunc (int) TUnit,cz), True)]
          (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)  -- Int
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc (TData ["A"] [] TUnit) TUnit,cz),True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A"]))))))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; SInst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit],cz)
          [(annz, "fff", (TFunc (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit]) TUnit,cz), True)]
          (func "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit, TData ["A"] [] TUnit]) TUnit,cz)
            (SCall annz (ECall annz (EVar annz "fff") (ETuple annz [(ECons annz ["A"]),(ECons annz ["A"])]))))))))
      `shouldBe` ([],
        SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SVar annz "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)
        (SVar annz "$fff$((A,A) -> ())$" (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)
        (mmm annz False (EVar annz "$fff$((A,A) -> ())$")
          (EFunc (annz {type_ = (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)}) FuncGlobal (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz) (SRet annz (EError annz 99)))
          (SCall annz
            (ECall (annz {type_ = (TUnit,cz)})
              (EVar (annz {type_ = (TFunc (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit]) TUnit,cz)}) "$fff$((A,A) -> ())$")
              (ETuple
                (annz {type_ = (TTuple [TData ["A"] [] TUnit,TData ["A"] [] TUnit],cz)}) [ECons (annz {type_ = (TData ["A"] [] TUnit,cz)}) ["A"],ECons (annz {type_ = (TData ["A"] [] TUnit,cz)}) ["A"]])))
          (SRet annz (EError annz 99))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit, cvc ("a","Xable")),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (bool,cz) False
        (SClass annz "Equalable" (cv "a") [(annz,"eq",(TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz),False)]
        (SVar annz "eq" (TFunc (TTuple [(TAny "a"),(TAny "a")]) (bool),cz)
        (SCall annz (ECall annz (EVar annz "eq") (ETuple annz [(ECons annz ["Bool"]),(ECons annz ["Int","1"])]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (bool,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (bool,cz)
          [(annz, "fff", (TFunc (bool) TUnit,cz), True)]
          (func "$fff$(Bool -> ())$" (TFunc (bool) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (int,cz)
                [(annz, "fff", (TFunc (int) TUnit,cz), True)]
                (func "$fff$(Int -> ())$" (TFunc (int) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SSeq annz
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Bool"])))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["Int"] [] [] TUnit False (SData annz Nothing ["Bool"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (SVar annz "fff$(Bool -> ())" (TFunc (TData ["Bool"]) TUnit) (SVar annz "fff$(Int -> ())" (TFunc (TData ["Int"]) TUnit) (SSeq annz (SCall annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["Int"]) TUnit,[]}) "fff$(Int -> ())") (ECons (annz {type_ = (TData ["Int","1"],[]}) ["Int","1"]))) (SCall annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["Bool"]) TUnit,[]}) "fff$(Bool -> ())") (ECons (annz {type_ = (TData ["Bool"],[]}) ["Bool"] (EUnit (annz {type_ = (TUnit,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) True
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"])))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit False (SData annz Nothing ["A","B"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc (TData ["A"]) TUnit) (SCall annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["A"]) TUnit,[]}) "fff$(A -> ())") (ECons (annz {type_ = (TData ["A","B"],[]}) ["A","B"] (EUnit (annz {type_ = (TUnit,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"]     [] TUnit,cz) True
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData ["A","B"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TData ["A","B"] [] TUnit) TUnit,cz), True)]
                (func "$fff$((A,B) -> ())$" (TFunc (TData ["A","B"] [] TUnit) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit False (SData annz Nothing ["A","B"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc (TData ["A"]) TUnit) (SVar annz "fff$(A.B -> ())" (TFunc (TData ["A","B"]) TUnit) (SCall annz (ECall (annz {type_ = (TUnit,[]}) (EVar (annz {type_ = (TFunc (TData ["A","B"]) TUnit,[]}) "fff$(A.B -> ())") (ECons (annz {type_ = (TData ["A","B"],[]}) ["A","B"] (EUnit (annz {type_ = (TUnit,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["A"] [] TUnit,cz) False
        (SData annz Nothing (TData ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc (TAny "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") TUnit,cz)
        (SInst annz "Xable" (TData ["A","B"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TData ["A","B"] [] TUnit) TUnit,cz), True)]
          (func "$fff$((A,B) -> ())$" (TFunc (TData ["A","B"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData ["A"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TData ["A"] [] TUnit) TUnit,cz), True)]
                (func "$fff$(A -> ())$" (TFunc (TData ["A"] [] TUnit) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["B"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc TUnit (TAny "b"),cz),False)]
        (SVar annz "fff" (TFunc TUnit (TAny "b"),cz)
        (SInst annz "X" (TData ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc TUnit (TData ["B"] [] TUnit),cz), True)]
          (func "$fff$(() -> B)$" (TFunc TUnit (TData ["B"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit False (SVar annz "fff" (TFunc TUnit (TAny "b" ["X"])) (SVar annz "fff$(() -> B)" (TFunc TUnit (TData ["B"])) (SCall annz (ECall (annz {type_ = (TData ["B"],[]}) (EVar (annz {type_ = (TFunc TUnit (TData ["B"]),[]}) "fff$(() -> B)") (EUnit (annz {type_ = (TUnit,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["B"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (SInst annz "X" (TData ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc (TAny "a") (TData ["B"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (SVar annz "fff$(a -> B)" (TFunc (TAny "a" []) (TData ["B"])) (SCall annz (ECall (annz {type_ = (TData ["B"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B"]),[]}) "fff$(a -> B)") (EUnit (annz {type_ = (TUnit,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (SInst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))))))
                  -- the problem is that SCall accept any return data
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit False (SData annz Nothing ["B2"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (SCall annz (ECall (annz {type_ = (TData ["B2"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {type_ = (TUnit,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (SInst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b1" (TData ["B1"] [] TUnit,cz)
                    (mmm annz False (EVar annz "b1")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit False (SData annz Nothing ["B2"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (SVar annz "b1" (TData ["B1"]) (mmm annz False (EVar annz "b1") (ECall (annz {type_ = (TData ["B1"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B1"]),[]}) "fff$(a -> B1)") (EUnit (annz {type_ = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc (TAny "a") (TAny "b"),cz),False)]
        (SVar annz "fff" (TFunc (TAny "a") (TAny "b"),cz)
        (SInst annz "X" (TData ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc (TAny "a") (TData ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc (TAny "a") (TData ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b2" (TData ["B2"] [] TUnit,cz)
                    (mmm annz False (EVar annz "b2")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit False (SData annz Nothing ["B2"] [] [] TUnit False (SVar annz "fff" (TFunc (TAny "a" []) (TAny "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc (TAny "a" []) (TData ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc (TAny "a" []) (TData ["B2"])) (SVar annz "b2" (TData ["B2"]) (mmm annz False (EVar annz "b2") (ECall (annz {type_ = (TData ["B2"],[]}) (EVar (annz {type_ = (TFunc (TAny "a" []) (TData ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {type_ = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
