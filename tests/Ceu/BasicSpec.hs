module Ceu.BasicSpec (main, spec) where

import Debug.Trace
import Test.Hspec
import qualified Data.Map as Map

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (annz, Ann(..))
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..), FuncType(..))
import Ceu.Grammar.Basic
import qualified Ceu.Grammar.Simplify as Simplify
import qualified Ceu.Grammar.TypeSys  as TypeSys

int   = TData False ["Int"]          []
bool  = TData False ["Bool"]         []
boolf = TData False ["Bool","False"] []
boolt = TData False ["Bool","True"]  []

main :: IO ()
main = hspec spec

mmm :: Ann -> Bool -> Exp -> Exp -> Stmt -> Stmt -> Stmt
mmm z b pat exp p1 p2 = SMatch z True b exp [(SNop z,pat,p1)]

mmm' :: Ann -> Bool -> Exp -> Exp -> Stmt -> Stmt -> Stmt
mmm' z b pat exp p1 p2 = SMatch z True b exp [(SNop z,pat,p1),(SNop z,EAny z, SRet z $ EError z (-2))]

func id tp p = SVar annz id tp
                (mmm annz False (EVar annz id)
                  (EFunc annz tp (EUnit annz) (SRet annz (EError annz 99)))
                  p
                  (SRet annz (EError annz 99)))

spec :: Spec
spec = do

  --describe "TODO" $ do

  describe "declarations" $ do

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (SData annz bool  Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
            (SCall annz (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
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
        (SData annz bool Nothing TUnit cz False
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "x" (bool,cz)
          (mmm annz False
            (ECons annz ["Bool","True"])
            (EVar  annz "x")
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["match is non exhaustive"]

    it "Bool ; True <- x" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz False
        (SData annz boolt Nothing TUnit cz False
        (SVar annz "x" (bool,cz)
          (mmm annz False
            (ECons annz ["Bool","True"])
            (EVar  annz "x")
            (SNop annz)
            (SNop annz))))))
      `shouldBe` ["match is non exhaustive"]

    it "Bool ; True <- x" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz  True
        (SData annz boolt Nothing TUnit cz False
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
    it "a:Bool ; 1 <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (bool,cz) (mmm annz True (ECons annz ["Int","1"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` ["types do not match : expected 'Int' : found 'Bool'"]
    it "a:Int ; 1 <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (int,cz) (mmm annz True (ECons annz ["Int","1"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` []

    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (bool,cz) (mmm annz True (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "a:Bool ; True <- a" $
      (fst $ TypeSys.go (prelude annz (SVar annz "a" (bool,cz) (mmm annz False (ECons annz ["Bool","True"]) (EVar annz "a") (SNop annz) (SNop annz)))))
        `shouldBe` ["match is non exhaustive"]

    checkCheckIt (SVar annz "a" (TUnit,cz) (SVar annz "a" (TUnit,cz) (SNop annz)))  ["variable 'a' is already declared"]
    checkCheckIt (prelude annz $ mmm annz False (EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))        ["variable 'a' is not declared"]

    checkCheckIt (prelude annz (SVar annz "umn" (TFunc FuncGlobal (int) (int),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (SNop annz) (SNop annz))))) ["variable 'b' is not declared"]


    it "a:() ; a <- -1" $
      (fst $ TypeSys.go
        (prelude annz
        (SVar annz "umn" (TFunc FuncGlobal (int) (int),cz)
        (SVar annz "a" (TUnit,cz)
        (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
      `shouldBe` ["types do not match : expected '(Int -> ())' : found '(Int -> Int)'"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'"]

    it "a:() ; a <- -b" $
      (fst $ TypeSys.go
        (prelude annz
        (SVar annz "umn" (TFunc FuncGlobal (int) (int),cz)
        (SVar annz "a" (TUnit,cz)
        (mmm annz False (EVar annz "a") (ECall annz (EVar annz "umn") (EVar annz "b")) (SNop annz) (SNop annz))))))
      `shouldBe` ["variable 'b' is not declared"]
      --`shouldBe` ["types do not match : expected '()' : found 'Int'", "variable 'b' is not declared"]

  checkCheckIt (prelude annz $ mmm annz False (EVar annz "a") (ECall annz (EVar annz "f") (ECons annz ["Int","1"])) (SNop annz) (SNop annz)) ["variable 'a' is not declared","variable 'f' is not declared"]
  checkCheckIt (SVar annz "x" (TTuple [TUnit,TUnit],cz) (mmm annz False (EVar annz "x") (EUnit annz) (SNop annz) (SNop annz)))  ["types do not match : expected '((),())' : found '()'"]
  checkCheckIt (prelude annz (SVar annz "x" (int,cz) (mmm annz False (EVar annz "x") (EUnit annz) (SNop annz) (SNop annz)))) ["types do not match : expected 'Int' : found '()'"]

  it "XXX: identity" $
    (fst $ TypeSys.go
      (prelude annz (SVar annz "identity" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "identity") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
      `shouldBe` []

  it "XXX: identity-rev" $
    (fst $ TypeSys.go
      (prelude annz (SVar annz "identity" (TFunc FuncGlobal int int,cz) (SVar annz "a" (TVar False "a",cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "identity") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
      `shouldBe` []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "ret" (TVar False "?",cz)
        (mmm annz False (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "ret" (TVar False "?",cz)
        (mmm annz True (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz True (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"],ECons annz ["Int","3"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (SVar annz "c" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b",EVar annz "c"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz)))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "f" (TFunc FuncGlobal TUnit (int),cz)
        (SVar annz "ret" (TVar False "?",cz)
        (mmm annz False (EVar annz "ret") (ECall annz (EVar annz "f") (EUnit annz)) (SNop annz) (SNop annz))))))
        `shouldBe` []

  describe "write!" $ do
    it "1 <- ret" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "ret" (int,cz)
        (mmm annz True (ECons annz ["Int","1"]) (EVar annz "ret") (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "1 <- ret" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "ret" (int,cz)
        (mmm annz False (ECons annz ["Int","1"]) (EVar annz "ret") (SNop annz) (SNop annz)))))
        `shouldBe` ["match is non exhaustive"]

  describe "functions" $ do
    it "func ~Int" $
      (fst $ TypeSys.go (SVar annz "f" (TFunc FuncGlobal TUnit (int),cz) (SNop annz)))
        `shouldBe` ["data 'Int' is not declared"]

    it "func f; func f" $
      TypeSys.go (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SNop annz)))
        `shouldBe` ([],SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SNop annz)))

    it "func f[a]; func f[0]" $
      TypeSys.go (SVar annz "f" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SNop annz)))
        `shouldBe` (["variable 'f' is already declared"],SVar annz "f" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SNop annz)))

    it "func f; func ~f" $
      TypeSys.go (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SVar annz "f" (TFunc FuncGlobal TUnit TAny,cz) (SNop annz)))
        `shouldBe` (["variable 'f' is already declared"],SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz) (SVar annz "f" (TFunc FuncGlobal TUnit TAny,cz) (SNop annz)))

    it "func first :: (a,a)->a ; var a::Int ; a = first((),1)" $
      (fst $ TypeSys.go (prelude annz (SVar annz "first" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (TVar False "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "first") (ETuple annz [(EUnit annz),(ECons annz ["Int","1"])])) (SNop annz) (SNop annz))))))
        `shouldBe`
          --["types do not match : expected '(a,a)' : found '((),Int)'","ambiguous iplementations for 'a' : '()', 'Int'"]
          --["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous implementations for 'a' : '()', 'Int', 'Int'"]
          ["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous implementations for 'a' : '()', 'Int'"]

{-
    checkCheckIt (prelude annz (SVar annz "first" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (TVar False "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "first") (ETuple annz [(ECons annz ["Int","1"]),(ECons annz ["Int","1"])])) (SNop annz) (SNop annz))))) []
-}

    it "() <- EArg" $
      (fst $ TypeSys.go
        (mmm annz False (EUnit annz) (EArg annz) (SNop annz) (SNop annz)))
      `shouldBe` []

    it "f <- func x = x" $
      (fst $ TypeSys.go
        (SVar annz "f" (TFunc FuncGlobal TUnit TUnit,cz)
        (mmm annz False (EVar annz "f")
          (EFunc annz (TFunc FuncGlobal TUnit TUnit,cz) (EUnit annz)
            (SRet annz (EArg annz)))
          (SNop annz)
          (SNop annz))))
        `shouldBe` []

    it "f : () -> a ; return f()" $
      (fst $ TypeSys.go
        (SVar annz "f" (TFunc FuncGlobal TUnit (TVar False "a"),cz)
        (SRet annz (ECall annz (EVar annz "f") (EUnit annz)))))
        `shouldBe` []

    it "f : a -> Int ; return f(1)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") (int),cz)
        (SRet annz (ECall annz (EVar annz "f") (ECons annz ["Int","1"]))))))
        `shouldBe` []

  describe "pattern matching" $ do
    it "1 = 1" $
      TypeSys.go (prelude annz $ mmm annz False (ECons annz ["Int","1"]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))
      `shouldBe` ([],SData annz (TData False ["Int"] []) Nothing TUnit cz False (SData annz (TData False ["Bool"] []) Nothing TUnit cz True (SData annz (TData False ["Bool","True"] []) Nothing TUnit cz False (SData annz (TData False ["Bool","False"] []) Nothing TUnit cz False (mmm annz{typec=(TBot,cz)} False (ECons annz{typec = (TData False ["Int"] [],cz)} ["Int","1"]) (ECons annz{typec=(TData False ["Int"] [],cz)} ["Int","1"]) (SNop annz) (SNop annz))))))
    it "1 <- 2" $
      TypeSys.go (prelude annz $ mmm annz True (ECons annz ["Int","1"]) (ECons annz ["Int","2"]) (SNop annz) (SNop annz))
      `shouldBe` (["match never succeeds : data mismatch"],SData annz (TData False ["Int"] []) Nothing TUnit cz False (SData annz (TData False ["Bool"] []) Nothing TUnit cz True (SData annz (TData False ["Bool","True"] []) Nothing TUnit cz False (SData annz (TData False ["Bool","False"] []) Nothing TUnit cz False (mmm' annz True (ECons annz{typec = (TData False ["Int"] [],cz)} ["Int","1"]) (ECons (annz {typec = (TData False ["Int"] [],cz)}) ["Int","2"]) (SNop annz) (SNop annz))))))
    it "_ = 1" $
      TypeSys.go (mmm annz False (EAny annz) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))
      `shouldBe` (["data 'Int.1' is not declared"],mmm annz{typec=(TBot,cz)} False (EAny annz) (ECons annz{typec=(TBot,cz)} ["Int","1"]) (SNop annz) (SNop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["match never succeeds"],SData annz int Nothing TUnit cz False (SData annz bool Nothing TUnit cz True (SData annz boolt Nothing TUnit cz False (SData annz boolf Nothing TUnit cz False (SVar annz{typec=(TBot,cz)} "x" (int,cz) (mmm annz{typec=(TBot,cz)} False (ETuple annz [EVar annz "x",(EAny annz)]) (ECons annz{typec=(TData False ["Int"] [],cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","1"]]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz int Nothing TUnit cz False (SData annz bool Nothing TUnit cz True (SData annz boolt Nothing TUnit cz False (SData annz boolf Nothing TUnit cz False (SVar (annz{typec = (TBot,cz)}) "x" (int,cz) (mmm (annz{typec = (TBot,cz)}) False (ETuple annz [EVar annz "x",(EAny annz)]) (ETuple (annz{typec = (TTuple [TData False ["Int"] [],TData False ["Int"] []],cz)}) [ECons (annz{typec = (TData False ["Int"] [],cz)}) ["Int","1"],ECons (annz{typec = (TData False ["Int"] [],cz)}) ["Int","1"]]) (SNop annz) (SNop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (SVar annz "y" (TTuple [TUnit, int],cz)
                (mmm annz False
                  (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"], (EAny annz)])
                  (ETuple annz [EVar annz "y", ECons annz ["Int","1"]])
                  (SNop annz)
                  (SNop annz)))))
      `shouldBe` ([],SData annz int Nothing TUnit cz False (SData annz bool Nothing TUnit cz True (SData annz boolt Nothing TUnit cz False (SData annz boolf Nothing TUnit cz False (SVar (annz{typec = (TBot,cz)}) "x" (int,cz) (SVar (annz{typec = (TBot,cz)}) "y" (TTuple [TUnit,int],cz) (mmm (annz{typec = (TBot,cz)}) False (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"],(EAny annz)]) (ETuple (annz{typec = (TTuple [TTuple [TUnit,int],TData False ["Int"] []],cz)}) [EVar (annz{typec = (TTuple [TUnit,int],cz)}) "y",ECons annz{typec = (TData False ["Int"] [],cz)} ["Int","1"]]) (SNop annz) (SNop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (int,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz int Nothing TUnit cz False (SData annz bool Nothing TUnit cz True (SData annz boolt Nothing TUnit cz False (SData annz boolf Nothing TUnit cz False (SVar annz "a" (int,cz) (mmm' annz True (EExp annz $ EVar annz{typec = (TBot,cz)} "a") (ECons annz{typec=(TData False ["Int"] [],cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (TUnit,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],SData annz int Nothing TUnit cz False (SData annz bool Nothing TUnit cz True (SData annz boolt Nothing TUnit cz False (SData annz boolf Nothing TUnit cz False (SVar annz "a" (TUnit,cz) (mmm' annz True (EExp annz $ EVar annz{typec = (TBot,cz)} "a") (ECons annz{typec=(TData False ["Int"] [],cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "data X with Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (SData annz (TData False ["Xxx"] []) Nothing int cz False (mmm annz True (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"])) (SRet annz (ECons annz ["Int","2"])) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (mmm annz True (ECons annz ["A"])  (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` ["data 'A' is not declared","match never succeeds : data mismatch"] --"types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz     True
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz True
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (SVar  annz "x" (TData False ["A","B"] [],cz)
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz True
        (mmm annz True (ECons annz ["A","B"]) (ECons annz ["A"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (prelude annz $ SData annz (TData False ["A"] []) Nothing TUnit cz  True (mmm annz True (ECons annz ["A"]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds : data mismatch"] --["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (SData annz (TData False ["A"] []) Nothing TUnit cz False (mmm annz False (ECall annz (ECons annz ["A"]) (EUnit annz)) (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (prelude annz $ SData annz (TData False ["A"] []) Nothing TUnit cz False (mmm annz False (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (ECons annz ["A"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["A"] []) Nothing TUnit cz True
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (SVar  annz "x" (TTuple [int, TData False ["A","B"] []],cz)
        (mmm annz True (ETuple annz [ECons annz ["Int","1"], ECons annz ["A"]]) (EVar annz "x") (SNop annz) (SNop annz)))))))
      `shouldBe` []

  --------------------------------------------------------------------------

  describe "new types" $ do

    it "Bool/True/False/Int" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SData annz int Nothing TUnit cz False
        (SNop annz))))))
      `shouldBe` []

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (SData annz boolt Nothing TUnit cz False
        (SData annz bool Nothing TUnit cz True
        (SData annz boolf Nothing TUnit cz False
        (SNop annz)))))
      `shouldBe` ["data 'Bool' is not declared"]

    it "Bool.True (w/o Bool)" $
      (fst $ TypeSys.go
        (SData annz (TData False ["Bool","True","Xxx"] []) Nothing TUnit cz False (SNop annz)))
      `shouldBe` ["data 'Bool.True' is not declared"]

    it "Int/Int" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz int Nothing TUnit cz False
        (SNop annz))))
      `shouldBe` ["data 'Int' is already declared"]

    it "~Int / x::Int" $
      (fst $ TypeSys.go
        (SVar annz "x" (int,cz) (SNop annz)))
      `shouldBe` ["data 'Int' is not declared"]

    it "x=Bool" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
          (SVar annz "x" (bool,cz)
            (mmm annz False (EVar annz "x") (ECons annz ["Bool"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Bool' is abstract"]

    it "Bool ; x=True" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
          (SVar annz "x" (bool,cz)
            (mmm annz False (EVar annz "x") (ECons annz ["Bool","True"]) (SNop annz) (SNop annz)))))))
      `shouldBe` []

    it "Bool ; (True == False)" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
            (SCall annz (ECall annz (EVar annz "==")
              (ETuple annz
                [ECons annz ["Bool","True"],
                 ECons annz ["Bool","False"]]))))))))
      `shouldBe` []

    it "Bool ; True <- (True == False)" $
      (fst $ TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
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
        (SData annz int Nothing TUnit cz True
        (SData annz bool Nothing TUnit cz True
        (SData annz boolt Nothing TUnit cz False
        (SData annz boolf Nothing TUnit cz False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(int),(int)]) (bool),cz)
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
          (mmm annz False (EVar annz "x") (ECons annz{typec=(bool,cz)} ["Bool","True"]) (SNop annz) (SNop annz))))
      `shouldBe` ["data 'Bool' is not declared","data 'Bool.True' is not declared"]

    it "data X with Int ; x <- X ()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["X"] []) Nothing int cz False
        (SVar annz "x" (TData False ["X"] [],cz)
          (mmm annz False (EVar annz "x") (ECons annz ["X"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","types do not match : expected 'X' : found '(Int -> X)'"]
      --["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (SData annz (TData False ["X"] []) Nothing int cz False
        (SVar annz "x" (TData False ["X"] [],cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","data 'Int.1' is not declared"]

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["X"]     []) Nothing int cz True
        (SData annz (TData False ["X","Y"] []) Nothing int cz False
        (SNop annz)))))
      `shouldBe` ([],SData annz int Nothing TUnit cz False (SData annz (TData False ["X"] []) Nothing int cz True (SData annz (TData False ["X","Y"] []) Nothing int cz False (SNop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["X"] []) Nothing (TTuple [int, int]) cz False
        (SVar annz "x" (TData False ["X"] [],cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","2"]])) (SNop annz) (SNop annz))))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (SData annz int Nothing TUnit cz False
          (SData annz (TData False ["X"] []) Nothing int cz False
          (SVar annz "x" (int,cz)
          (mmm annz False (ECall annz (ECons annz ["X"]) (EVar annz "x")) (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (SData annz int Nothing TUnit cz False
          (SData annz (TData False ["X"] []) Nothing int cz False
          (SVar annz "x" (int,cz)
          (mmm annz False (ECall annz (ECons annz ["X"]) (EVar annz "x")) (ECons annz ["X"]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match never succeeds"]
          --["types do not match : expected 'X' : found '(Int -> X)'"]
          --["types do not match : expected 'Int' : found '()'"]

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
