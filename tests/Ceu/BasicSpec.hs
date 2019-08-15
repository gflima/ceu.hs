module Ceu.BasicSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Ann          (annz, Ann(..))
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..), FuncType(..))
import Ceu.Grammar.Basic
import qualified Ceu.Grammar.Simplify as Simplify
import qualified Ceu.Grammar.TypeSys  as TypeSys

int   = TData False ["Int"]          [] TUnit
bool  = TData False ["Bool"]         [] TUnit
boolf = TData False ["Bool","False"] [] TUnit
boolt = TData False ["Bool","True"]  [] TUnit

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
        (SData annz Nothing (bool, cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
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
  checkCheckIt (prelude annz (SVar annz "identity" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (SVar annz "a" (int,cz) (mmm annz False (EVar annz "a") (ECall annz (EVar annz "identity") (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))) []

  describe "write" $ do
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (TVar False "?",cz)
        (mmm annz False (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` []
    it "ret = 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "ret" (TVar False "?",cz)
        (mmm annz True (EVar annz "ret") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` []
    it "(a,b) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz True (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match is exhaustive"]
    it "(a,b) = (1,2,3)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"],ECons annz ["Int","3"]]) (SNop annz) (SNop annz))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?)' : found '(Int.1,Int.2,Int.3)'"]
    it "(a,b,c) = (1,2)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "a" (TVar False "?",cz)
        (SVar annz "b" (TVar False "?",cz)
        (SVar annz "c" (TVar False "?",cz)
        (mmm annz False (ETuple annz [EVar annz "a",EVar annz "b",EVar annz "c"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]]) (SNop annz) (SNop annz)))))))
        `shouldBe` ["match never succeeds : arity mismatch"]
          --["types do not match : expected '(?,?,?)' : found '(Int.1,Int.2)'"]
    it "ret = f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SVar annz "f" (TFunc FuncGlobal TUnit (int),cz)
        (SVar annz "ret" (TVar False "?",cz)
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
      --["types do not match : expected '(a,a)' : found '((),Int)'","ambiguous instances for 'a' : '()', 'Int'"]
          ["types do not match : expected '(((),Int) -> Int)' : found '((a,a) -> a)'","ambiguous instances for 'a' : '()', 'Int', 'Int'"]

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
        (SData annz Nothing (int,cz) False
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") (int),cz)
        (SRet annz (ECall annz (EVar annz "f") (ECons annz ["Int","1"]))))))
        `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (SData annz Nothing (int,cz) False
        (SClass annz "X" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") (int),cvc ("a","X")),False)]
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (int),cvc ("a","X"))
        (SInst annz "X" (int,cz)
            [(annz,"fff",(TFunc FuncGlobal (int) (int),cz),True)]
            (SVar annz "fff" (TFunc FuncGlobal (int) (int),cz)
            (mmm annz False
              (EVar annz "fff")
              (EFunc annz (TFunc FuncGlobal (int) (int),cz) (EUnit annz)
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
      `shouldBe` ([],SData annz Nothing (TData False ["Int"] [] TUnit,cz) False (SData annz Nothing (TData False ["Bool"] [] TUnit,cz) True (SData annz Nothing (TData False ["Bool","True"] [] TUnit,cz) False (SData annz Nothing (TData False ["Bool","False"] [] TUnit,cz) False (mmm annz{typec=(TBot,cz)} False (ECons annz{typec = (TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (ECons annz{typec=(TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz))))))
    it "1 <- 2" $
      TypeSys.go (prelude annz $ mmm annz True (ECons annz ["Int","1"]) (ECons annz ["Int","2"]) (SNop annz) (SNop annz))
      `shouldBe` (["match never succeeds : data mismatch"],SData annz Nothing (TData False ["Int"] [] TUnit,cz) False (SData annz Nothing (TData False ["Bool"] [] TUnit,cz) True (SData annz Nothing (TData False ["Bool","True"] [] TUnit,cz) False (SData annz Nothing (TData False ["Bool","False"] [] TUnit,cz) False (mmm' annz True (ECons annz{typec = (TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (ECons (annz {typec = (TData False ["Int"] [] TUnit,cz)}) ["Int","2"]) (SNop annz) (SNop annz))))))
    it "_ = 1" $
      TypeSys.go (mmm annz False (EAny annz) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))
      `shouldBe` (["data 'Int.1' is not declared"],mmm annz{typec=(TBot,cz)} False (EAny annz) (ECons annz{typec=(TBot,cz)} ["Int","1"]) (SNop annz) (SNop annz))
    it "(x,_) = 1" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["match never succeeds"],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz{typec=(TBot,cz)} "x" (int,cz) (mmm annz{typec=(TBot,cz)} False (ETuple annz [EVar annz "x",(EAny annz)]) (ECons annz{typec=(TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "(x,_) = (1,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (mmm annz False (ETuple annz [EVar annz "x", (EAny annz)]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","1"]]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar (annz{typec = (TBot,cz)}) "x" (int,cz) (mmm (annz{typec = (TBot,cz)}) False (ETuple annz [EVar annz "x",(EAny annz)]) (ETuple (annz{typec = (TTuple [TData False ["Int"] [] TUnit,TData False ["Int"] [] TUnit],cz)}) [ECons (annz{typec = (TData False ["Int"] [] TUnit,cz)}) ["Int","1"],ECons (annz{typec = (TData False ["Int"] [] TUnit,cz)}) ["Int","1"]]) (SNop annz) (SNop annz)))))))

    it "((_,x),_) = (y,1)" $
      TypeSys.go (prelude annz
            (SVar annz "x" (int,cz)
              (SVar annz "y" (TTuple [TUnit, int],cz)
                (mmm annz False
                  (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"], (EAny annz)])
                  (ETuple annz [EVar annz "y", ECons annz ["Int","1"]])
                  (SNop annz)
                  (SNop annz)))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar (annz{typec = (TBot,cz)}) "x" (int,cz) (SVar (annz{typec = (TBot,cz)}) "y" (TTuple [TUnit,int],cz) (mmm (annz{typec = (TBot,cz)}) False (ETuple annz [ETuple annz [(EAny annz),EVar annz "x"],(EAny annz)]) (ETuple (annz{typec = (TTuple [TTuple [TUnit,int],TData False ["Int"] [] TUnit],cz)}) [EVar (annz{typec = (TTuple [TUnit,int],cz)}) "y",ECons annz{typec = (TData False ["Int"] [] TUnit,cz)} ["Int","1"]]) (SNop annz) (SNop annz))))))))

    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (int,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz "a" (int,cz) (mmm' annz True (EExp annz $ EVar annz{typec = (TBot,cz)} "a") (ECons annz{typec=(TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))
    it "`a` = 1" $
      TypeSys.go (prelude annz
        (SVar annz "a" (TUnit,cz) (mmm annz True (EExp annz $ EVar annz "a") (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` (["types do not match : expected '()' : found 'Int'"],SData annz Nothing (int,cz) False (SData annz Nothing (bool,cz) True (SData annz Nothing (boolt,cz) False (SData annz Nothing (boolf,cz) False (SVar annz "a" (TUnit,cz) (mmm' annz True (EExp annz $ EVar annz{typec = (TBot,cz)} "a") (ECons annz{typec=(TData False ["Int"] [] TUnit,cz)} ["Int","1"]) (SNop annz) (SNop annz)))))))

    it "data X with Int ; X 1 <- X 2" $
      (fst $ TypeSys.go (prelude annz
        (SData annz Nothing (TData False ["Xxx"] [] int,cz) False (mmm annz True (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"])) (SRet annz (ECons annz ["Int","2"])) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "A <- 1" $
      (fst $ TypeSys.go (mmm annz True (ECons annz ["A"])  (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` ["data 'A' is not declared","match never succeeds : data mismatch"] --"types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A.B ; A <- A.B" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz)     True
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz)))))
      `shouldBe` []

    it "A ; A.B ; x:A.B ; A <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"]     [] TUnit,cz) True
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (SVar  annz "x" (TData False ["A","B"] [] TUnit,cz)
        (mmm annz False (ECons annz ["A"]) (ECons annz ["A","B"]) (SNop annz) (SNop annz))))))
      `shouldBe` []

    it "A ; A.B ; A.B <- A" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"]     [] TUnit,cz) False
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) True
        (mmm annz True (ECons annz ["A","B"]) (ECons annz ["A"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["match never succeeds : data mismatch"]
        --["types do not match : expected 'A.B' : found 'A'"]

    it "A ; A <- 1" $
      (fst $ TypeSys.go (prelude annz $ SData annz Nothing (TData False ["A"] [] TUnit,cz) True (mmm annz True (ECons annz ["A"]) (ECons annz ["Int","1"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds : data mismatch"] --["types do not match : expected 'A' : found 'Int.1'"]

    it "A ; A <- A 1" $
      (fst $ TypeSys.go (SData annz Nothing (TData False ["A"] [] TUnit,cz) False (mmm annz False (ECall annz (ECons annz ["A"]) (EUnit annz)) (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected '()' : found 'Int.1'"]

    it "A ; A 1 <- A" $
      (fst $ TypeSys.go (prelude annz $ SData annz Nothing (TData False ["A"] [] TUnit,cz) False (mmm annz False (ECall annz (ECons annz ["A"]) (ECons annz ["Int","1"])) (ECons annz ["A"]) (SNop annz) (SNop annz))))
      `shouldBe` ["match never succeeds"] --["types do not match : expected 'Int.1' : found '()'"]

    it "A ; A.B ; x:(Int,A.B) ; (1,A) <- x" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) True
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (SVar  annz "x" (TTuple [int, TData False ["A","B"] [] TUnit],cz)
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
        (SData annz Nothing (TData False ["Bool","True","Xxx"] [] TUnit,cz) False (SNop annz)))
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
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(bool),(bool)]) (bool),cz)
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
        (SData annz Nothing (int,cz) True
        (SData annz Nothing (bool,cz) True
        (SData annz Nothing (boolt,cz) False
        (SData annz Nothing (boolf,cz) False
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
        (SData annz Nothing (TData False ["X"] [] int,cz) False
        (SVar annz "x" (TData False ["X"] [] TUnit,cz)
          (mmm annz False (EVar annz "x") (ECons annz ["X"]) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","types do not match : expected 'X' : found '(Int -> X)'"]
      --["types do not match : expected 'Int' : found '()'"]
      -- ["types do not match : 'Int' is not supertype of '()'"]

    it "data X with Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["X"] [] int,cz) False
        (SVar annz "x" (TData False ["X"] [] (int),cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz)))))
      `shouldBe` ["data 'Int' is not declared","data 'Int' is not declared","data 'Int.1' is not declared"]

    it "data X with Int ; data X.Y with Int" $
      (TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["X"]     [] int,cz) True
        (SData annz Nothing (TData False ["X","Y"] [] int,cz) False
        (SNop annz)))))
      `shouldBe` ([],SData annz Nothing (int,cz) False (SData annz Nothing (TData False ["X"] [] int,cz) True (SData annz Nothing (TData False ["X","Y"] [] int,cz) False (SNop annz))))

    it "data X with (Int,Int)" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["X"] [] (TTuple [int, int]),cz) False
        (SVar annz "x" (TData False ["X"] [] (TTuple [int, int]),cz)
          (mmm annz False (EVar annz "x") (ECall annz (ECons annz ["X"]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","2"]])) (SNop annz) (SNop annz))))))
      `shouldBe` []

    describe "pattern matching" $ do

      it "data X with Int ; x:Int ; X x <- X 1" $
        (fst $ TypeSys.go
          (SData annz Nothing (int,cz) False
          (SData annz Nothing (TData False ["X"] [] int,cz) False
          (SVar annz "x" (int,cz)
          (mmm annz False (ECall annz (ECons annz ["X"]) (EVar annz "x")) (ECall annz (ECons annz ["X"]) (ECons annz ["Int","1"])) (SNop annz) (SNop annz))))))
        `shouldBe` []

      it "data X with Int ; x:Int ; X x <- X ()" $
        (fst $ TypeSys.go
          (SData annz Nothing (int,cz) False
          (SData annz Nothing (TData False ["X"] [] int,cz) False
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
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cvc ("a","X"))
        (SClass annz "Y" (cv "a") []
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cvc ("a","Y"))
        (SNop annz))))))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst $ TypeSys.go
        (SClass annz "X" (cv "a") []
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","X"))
        (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SNop annz)))))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      TypeSys.go
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz)
        (SNop annz)))
      `shouldBe` (["data 'Bool' is not declared"],(SVar annz "==" (TFunc FuncGlobal (TTuple [TVar False "a",TVar False "a"]) (bool),cz) (SNop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz)
        (SNop annz))))
      `shouldBe` ([],SData annz Nothing (bool,cz) True (SVar annz "==" (TFunc FuncGlobal (TTuple [TVar False "a",TVar False "a"]) (bool),cz) (SNop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz Nothing (bool,cz) True
        (SClass annz "Equalable" (cv "a") []
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool), cvc ("a","Equalable"))
        (SNop annz))))
      `shouldBe` ([],SData annz Nothing (bool,cz) True (SNop annz))

    it "A ; Xable ; inst ; inst" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
                [(annz,"fff",(TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz),True)]
                (SVar annz "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
                (SSeq annz
                  (SNop annz)
                  (SNop annz))))
            )))))))
      `shouldBe` ["instance 'Xable (A)' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz) []
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz,"fff2",(TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz),True)]
          (func "fff2" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz) []
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc FuncGlobal (TData False ["A"] [] TUnit) (int),cz),True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) (int),cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "X" (TData False ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc FuncGlobal (int) TUnit,cz),True)]
          (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
          (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)        -- a
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)                          -- A
          [(annz, "fff", (TFunc FuncGlobal (int) TUnit,cz), True)]
          (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)  -- Int
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz,"fff",(TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz),True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A"]))))))))))
      `shouldBe` []

    it "A ; Xable.fff(a) ; SInst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TTuple [TData False ["A"] [] TUnit, TData False ["A"] [] TUnit],cz)
          [(annz, "fff", (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit, TData False ["A"] [] TUnit]) TUnit,cz), True)]
          (func "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit, TData False ["A"] [] TUnit]) TUnit,cz)
            (SCall annz (ECall annz (EVar annz "fff") (ETuple annz [(ECons annz ["A"]),(ECons annz ["A"])]))))))))
      `shouldBe` ([],
        SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SVar annz "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit]) TUnit,cz)
        (SVar annz "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit]) TUnit,cz)
        (mmm annz False (EVar annz "$fff$((A,A) -> ())$")
          (EFunc (annz {typec = (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit]) TUnit,cz)}) (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit]) TUnit,cz) (EUnit annz) (SRet annz (EError annz 99)))
          (SCall annz
            (ECall (annz {typec = (TUnit,cz)})
              (EVar (annz {typec = (TFunc FuncGlobal (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit]) TUnit,cz)}) "$fff$((A,A) -> ())$")
              (ETuple
                (annz {typec = (TTuple [TData False ["A"] [] TUnit,TData False ["A"] [] TUnit],cz)}) [ECons (annz {typec = (TData False ["A"] [] TUnit,cz)}) ["A"],ECons (annz {typec = (TData False ["A"] [] TUnit,cz)}) ["A"]])))
          (SRet annz (EError annz 99))))))

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable")),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (bool,cz) False
        (SClass annz "Equalable" (cv "a") [(annz,"eq",(TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz),False)]
        (SVar annz "eq" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz)
        (SCall annz (ECall annz (EVar annz "eq") (ETuple annz [(ECons annz ["Bool"]),(ECons annz ["Int","1"])]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (SData annz Nothing (int,cz) False
        (SData annz Nothing (bool,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (bool,cz)
          [(annz, "fff", (TFunc FuncGlobal (bool) TUnit,cz), True)]
          (func "$fff$(Bool -> ())$" (TFunc FuncGlobal (bool) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (int,cz)
                [(annz, "fff", (TFunc FuncGlobal (int) TUnit,cz), True)]
                (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SSeq annz
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Bool"])))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["Int"] [] [] TUnit (SData annz Nothing ["Bool"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(Bool -> ())" (TFunc FuncGlobal (TData False ["Bool"]) TUnit) (SVar annz "fff$(Int -> ())" (TFunc FuncGlobal (TData False ["Int"]) TUnit) (SSeq annz (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["Int"]) TUnit,[]}) "fff$(Int -> ())") (ECons (annz {typec = (TData False ["Int","1"],[]}) ["Int","1"]))) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["Bool"]) TUnit,[]}) "fff$(Bool -> ())") (ECons (annz {typec = (TData False ["Bool"],[]}) ["Bool"] (EUnit (annz {typec = (TUnit,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) True
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"])))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit (SData annz Nothing ["A","B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc FuncGlobal (TData False ["A"]) TUnit) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["A"]) TUnit,[]}) "fff$(A -> ())") (ECons (annz {typec = (TData False ["A","B"],[]}) ["A","B"] (EUnit (annz {typec = (TUnit,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"]     [] TUnit,cz) True
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz), True)]
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData False ["A","B"] [] TUnit,cz)
                [(annz, "fff", (TFunc FuncGlobal (TData False ["A","B"] [] TUnit) TUnit,cz), True)]
                (func "$fff$((A,B) -> ())$" (TFunc FuncGlobal (TData False ["A","B"] [] TUnit) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit (SData annz Nothing ["A","B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc FuncGlobal (TData False ["A"]) TUnit) (SVar annz "fff$(A.B -> ())" (TFunc FuncGlobal (TData False ["A","B"]) TUnit) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["A","B"]) TUnit,[]}) "fff$(A.B -> ())") (ECons (annz {typec = (TData False ["A","B"],[]}) ["A","B"] (EUnit (annz {typec = (TUnit,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["A"] [] TUnit,cz) False
        (SData annz Nothing (TData False ["A","B"] [] TUnit,cz) False
        (SClass annz "Xable" (cv "a") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A","B"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TData False ["A","B"] [] TUnit) TUnit,cz), True)]
          (func "$fff$((A,B) -> ())$" (TFunc FuncGlobal (TData False ["A","B"] [] TUnit) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData False ["A"] [] TUnit,cz)
                [(annz, "fff", (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz), True)]
                (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] [] TUnit) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["B"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc FuncGlobal TUnit (TVar False "b"),cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal TUnit (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal TUnit (TData False ["B"] [] TUnit),cz), True)]
          (func "$fff$(() -> B)$" (TFunc FuncGlobal TUnit (TData False ["B"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal TUnit (TVar False "b" ["X"])) (SVar annz "fff$(() -> B)" (TFunc FuncGlobal TUnit (TData False ["B"])) (SCall annz (ECall (annz {typec = (TData False ["B"],[]}) (EVar (annz {typec = (TFunc FuncGlobal TUnit (TData False ["B"]),[]}) "fff$(() -> B)") (EUnit (annz {typec = (TUnit,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["B"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B"])) (SCall annz (ECall (annz {typec = (TData False ["B"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B"]),[]}) "fff$(a -> B)") (EUnit (annz {typec = (TUnit,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData False ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))))))
                  -- the problem is that SCall accept any return data
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SCall annz (ECall (annz {typec = (TData False ["B2"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {typec = (TUnit,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData False ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b1" (TData False ["B1"] [] TUnit,cz)
                    (mmm annz False (EVar annz "b1")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SVar annz "b1" (TData False ["B1"]) (mmm annz False (EVar annz "b1") (ECall (annz {typec = (TData False ["B1"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"]),[]}) "fff$(a -> B1)") (EUnit (annz {typec = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (SData annz Nothing (TData False ["B1"] [] TUnit,cz) False
        (SData annz Nothing (TData False ["B2"] [] TUnit,cz) False
        (SClass annz "X" (cv "b") [(annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False)]
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [] TUnit,cz)
          [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz), True)]
          (func "$fff$(a -> B1)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] [] TUnit),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [] TUnit,cz)
                [(annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz), True)]
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] [] TUnit),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b2" (TData False ["B2"] [] TUnit,cz)
                    (mmm annz False (EVar annz "b2")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SVar annz "b2" (TData False ["B2"]) (mmm annz False (EVar annz "b2") (ECall (annz {typec = (TData False ["B2"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {typec = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

  --------------------------------------------------------------------------

    where
    checkIt' ck p b   =
      (it ((if b==[] then "pass" else "fail") ++ ": todo") $
      (ck p) `shouldBe` b)
    checkCheckIt :: Stmt -> Errors -> Spec
    checkCheckIt p b = checkIt' (fst . (TypeSys.go)) p b
