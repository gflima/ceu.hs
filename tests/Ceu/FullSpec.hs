module Ceu.FullSpec (main, spec) where

import Test.Hspec
import Text.Printf
import Debug.Trace
import Data.Map (fromList, singleton)

import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..), FuncType(..))
import Ceu.Grammar.Ann          (Ann(typec),annz)

import qualified Ceu.Grammar.Basic as B
import qualified Ceu.Eval as E

import Ceu.Grammar.Full.Full
import Ceu.Grammar.Full.Eval
import qualified Ceu.Grammar.Full.Compile.Scope as Scope
import qualified Ceu.Grammar.Full.Compile.Func  as Func

main :: IO ()
main = hspec spec

setb z chk loc exp p1 p2 = B.SMatch  z True chk   exp [(B.SNop z,loc,p1)]
set  z     loc exp p1 p2 =   SMatch  z True False exp [(  SNop z,loc,p1)]
set' z chk loc exp p1 p2 =   SMatch  z True chk   exp [(  SNop z,loc,p1)]

spec :: Spec
spec = do

{-
  describe "TODO" $ do
    it "TODO" $
      compile' (SSeq annz (SData annz Nothing ["Int"] [] TUnit) (SSeq annz (SSeq annz (SVar annz "x" (TData False ["Int"])) (SNop annz)) (SSeq annz (SSet annz False (EVar annz "x") (ECons annz ["Int","1"])) (SRet annz (ECons annz ["Int","1"])))))
      `shouldBe` ([], (B.SVar annz "x" TUnit (B.SNop annz)))
-}

  --------------------------------------------------------------------------
            --"   func f1 x : (a -> Bool) do return f2 x end",

  describe "EFunc.compile" $ do

    it "func id : (a->a) do end" $ do
      (map_stmt' (id2,Func.remEFuncPar,id) . map_stmt' (f2 Func.remSFunc,id,id))
       (SFunc annz "id" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (EAny annz) (SNop annz))
      `shouldBe` (SVar annz "id" (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz)
                  (Just
                    (EFunc' annz (TFunc FuncGlobal (TVar False "a") (TVar False "a"),cz) (SNop annz))))

  describe "Scope.compile" $ do

    describe "var:" $ do
      it "var x" $ do
        (map_stmt' (f2 Scope.setScope,id,id)) (SVar annz "x" (TUnit,cz) Nothing)
        `shouldBe` (SVarS annz "x" (TUnit,cz) Nothing (SNop annz))

      it "var x; (SNop annz)" $ do
        (map_stmt' (f2 Scope.setScope,id,id)) (SSeq annz (SVar annz "x" (TUnit,cz) Nothing) (SNop annz))
        `shouldBe` (SVarS annz "x" (TUnit,cz) Nothing (SNop annz))

      it "var x <- 1 ; (SNop annz)" $ do
        (map_stmt' (f2 Scope.setScope,id,id)) (SSeq annz (SVar annz "x" (int,cz) Nothing) (SSeq annz (SSet annz True False (EVar annz "x") (ECons annz ["Int","1"])) (SNop annz)))
        `shouldBe` (SVarS annz "x" (int,cz) Nothing (SSeq annz (SSet annz True False (EVar annz "x") (ECons annz ["Int","1"])) (SNop annz)))

      it "scope var x end ; var y" $ do
        (map_stmt' (f2 Scope.remSScope,id,id) . map_stmt' (f2 Scope.setScope,id,id)) (SSeq annz (SScope annz (SVar annz "x" (TUnit,cz) Nothing)) (SVar annz "y" (TUnit,cz) Nothing))
        `shouldBe` SSeq annz (SVarS annz "x" (TUnit,cz) Nothing (SNop annz)) (SVarS annz "y" (TUnit,cz) Nothing (SNop annz))

      it "scope var x end ; x=1" $ do
        compile' (SSeq annz (SScope annz (SVar annz "x" (int,cz) Nothing)) (SSet annz True False (EVar annz "x") (ECons annz ["Int","1"])))
        `shouldBe` (["data 'Int' is not declared","variable 'x' is not declared","data 'Int.1' is not declared"], B.SSeq annz (B.SVar annz "x" (int,cz) (B.SNop annz)) (setb annz False (B.EVar annz "x") (B.ECons (annz{typec=(TBot,cz)}) ["Int","1"]) (B.SNop annz) (B.SRet annz (B.EError annz (-2)))))

  describe "compile" $ do

    it "if" $
      (snd . compile)
        (SSeq annz
            (set annz
                (EExp annz (EVar annz "_true"))
                (ECall annz (ECons annz ["Bool","False"]) (EUnit annz))
                (SNop annz)
                (SNop annz))
            (SRet annz (ECons annz ["Int","10"])))
      `shouldBe` SSeq annz (set' annz False (EExp annz (EVar annz "_true")) (ECall annz (ECons annz ["Bool","False"]) (EUnit annz)) (SNop annz) (SNop annz)) (SRet annz (ECons annz ["Int","10"]))

  --------------------------------------------------------------------------

  describe "compile'" $ do

    it "var x;" $ do
      compile' (SVarS annz "x" (TUnit,cz) Nothing (SNop annz))
      `shouldBe` ([], (B.SVar annz "x" (TUnit,cz) (B.SNop annz)))

    it "do var x; x = 1 end" $ do
      compile' (SVarS annz "x" (int,cz) Nothing (set' annz False (EVar annz "x") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.SVar annz "x" (int,cz) (setb annz False (B.EVar annz "x") (B.ECons annz{typec=(TBot,cz)} ["Int","1"]) (B.SNop annz) (B.SNop annz))))

    it "do var x; x = 1 end" $ do
      compile' (SVarS annz "x" (int,cz) Nothing (set' annz False (EVar annz "x") (ECons annz ["Int","1"]) (SNop annz) (SNop annz)))
      `shouldBe` (["data 'Int' is not declared","data 'Int.1' is not declared"], (B.SVar annz "x" (int,cz) (setb annz False (B.EVar annz "x") (B.ECons annz{typec=(TBot,cz)} ["Int","1"]) (B.SNop annz) (B.SNop annz))))

  --------------------------------------------------------------------------

  describe "go" $ do
    it "ret 1" $ do
      go (prelude annz $ SRet annz (ECons annz ["Int","1"]))
      `shouldBe` Right (E.EData ["Int","1"] E.EUnit)

    it "data X with Int ; x:Int ; X 1 <- X 2" $ do
      go (prelude annz $ SSeq annz (SData annz (TData False ["Xxx"] []) Nothing int cz False) (SSeq annz (SSet annz True False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"]))) (SRet annz (ECons annz ["Int","2"]))))
      `shouldBe`
        Left ["match never succeeds : data mismatch"] --["types do not match : expected 'Int.1' : found 'Int.2'"]

    it "call (func () : (() -> ()) do end)" $ do
      go (prelude annz $ SSeq annz
          (SCall annz (ECall annz
                        (EFunc' annz (TFunc FuncGlobal TUnit TUnit,cz)
                          (SRet annz (EUnit annz))) (EUnit annz)))
          (SRet annz (ECons annz ["Int","10"])))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)

    it "ret (func () : (() -> Int) do ret 10 end) ()" $ do
      go (prelude annz $ SRet annz
            (ECall annz
              (EFunc' annz (TFunc FuncGlobal TUnit (int),cz)
                (SRet annz (ECons annz ["Int","10"])))
              (EUnit annz)))
      `shouldBe` Right (E.EData ["Int","10"] E.EUnit)
  --------------------------------------------------------------------------

  describe "typeclass:" $ do

    it "class/inst/0" $ do
      (fst.compile)
        (SInst annz "F3able" (int,cz)
          (SFunc annz "f3" (TFunc FuncGlobal (TVar False "Int") (int),cz) (EAny annz)
            (SRet annz (ECons annz ["Int","10"]))))
      `shouldBe` ["interface 'F3able' is not declared","unexpected implementation of 'f3'"]

    it "X.f ; X.f" $
      (fst.compile)
        (SSeq annz
          (SClass annz "X" (cv "a") (SNop annz))
          (SClass annz "X" (cv "a") (SNop annz)))
      `shouldBe` ["interface 'X' is already declared"]

    it "X.f ; Y.f" $
      (fst.compile')
        (SSeq annz
          (SClass annz "X" (cv "a")
            (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SClass annz "Y" (cv "a")
            (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing)))
      `shouldBe` ["variable 'f' is already declared"]

    it "X.f ; f" $
      (fst.compile')
        (SSeq annz
          (SClass annz "X" (cv "a")
            (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","X")) Nothing))
          (SVar annz "f" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
      `shouldBe` ["variable 'f' is already declared"]

    it "~Bool ; Equalable ; (==)" $
      (fst.compile')
        (SClass annz "Equalable" (cv "a")
          (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz) Nothing))
      `shouldBe` ["data 'Bool' is not declared"]

    it "A ; Xable ; inst ; inst" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99)))))))))
      `shouldBe` ["implementation of 'Xable' for 'A' is already declared"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SNop annz))))
      `shouldBe` ["missing implementation of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff2" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))))
      `shouldBe` ["missing implementation of 'fff1'","unexpected implementation of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SNop annz))))
      `shouldBe` ["missing implementation of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) int,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) int,cz) (EVar annz "x") (SRet annz (EError annz 99)))))))))
      --`shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]
      --`shouldBe` ["types do not match : expected '((($Xable$,A) -> Int) -> $Xable$)' : found '((($Xable$,a) -> ()) -> $Xable$)'"]
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'","types do not match : expected '((($Xable$,A) -> Int) -> $Xable$)' : found '((($Xable$,a) -> ()) -> $Xable$)'"]

    it "A ; Xable a ; inst X A" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a") 
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
          (SInst annz "X" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal int TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal int TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99)))))))))
      `shouldBe` ["interface 'X' is not declared","unexpected implementation of 'fff'","data '$X$' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing)) -- a
          (SInst annz "Xable" (TData False ["A"] [],cz)                             -- A
            (SVar annz "fff" (TFunc FuncGlobal int TUnit,cz)                        -- int
              (Just (EFunc annz (TFunc FuncGlobal int TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A"]))))))
      `shouldBe` []

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable")) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))))))
      `shouldBe` ["variable 'fff' has no associated implementation for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz bool Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Equalable" (cv "a")
            (SVar annz "eq" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz) Nothing))
          (SCall annz (ECall annz (EVar annz "eq") (ETuple annz [(ECons annz ["Bool"]),(ECons annz ["Int","1"])]))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous implementations for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SData annz bool Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (bool,cz)
            (SVar annz "fff" (TFunc FuncGlobal bool TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal bool TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "Xable" (int,cz)
            (SVar annz "fff" (TFunc FuncGlobal int TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal int TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Bool"])))))))))
      `shouldBe` []

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz True)
        (SSeq annz
          (SData annz (TData False ["A","B"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"])))))))
      `shouldBe` []

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz True)
        (SSeq annz
          (SData annz (TData False ["A","B"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A","B"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))
      `shouldBe` []

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["A"] []) Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["A","B"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "Xable" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz) Nothing))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A","B"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "Xable" (TData False ["A"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
              (Just (EFunc annz (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["B"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "b")
            (SVar annz "fff" (TFunc FuncGlobal TUnit (TVar False "b"),cz) Nothing))
        (SSeq annz
          (SInst annz "X" (TData False ["B"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal TUnit (TData False ["B"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal TUnit (TData False ["B"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))
      `shouldBe` []

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["B"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "b")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz) Nothing))
        (SSeq annz
          (SInst annz "X" (TData False ["B"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))
      `shouldBe` []

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["B1"] []) Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["B2"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "b")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz) Nothing))
        (SSeq annz
          (SInst annz "X" (TData False ["B1"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "X" (TData False ["B2"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))
                  -- the problem is that SCall accept any return data
      `shouldBe` []

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["B1"] []) Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["B2"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "b")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz) Nothing))
        (SSeq annz
          (SInst annz "X" (TData False ["B1"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "X" (TData False ["B2"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SVar annz "b1" (TData False ["B1"] [],cz)
            (Just (ECall annz (EVar annz "fff") (EUnit annz)))))))))
      `shouldBe` []

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst.compile')
        (SSeq annz
          (SData annz (TData False ["B1"] []) Nothing TUnit cz False)
        (SSeq annz
          (SData annz (TData False ["B2"] []) Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "b")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz) Nothing))
        (SSeq annz
          (SInst annz "X" (TData False ["B1"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
        (SSeq annz
          (SInst annz "X" (TData False ["B2"] [],cz)
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
              (Just (EFunc annz (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz) (EVar annz "x") (SRet annz (EError annz 99))))))
          (SVar annz "b2" (TData False ["B2"] [],cz)
            (Just (ECall annz (EVar annz "fff") (EUnit annz)))))))))
      `shouldBe` []

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst.compile')
        (SSeq annz
          (SData annz int Nothing TUnit cz False)
        (SSeq annz
          (SClass annz "X" (cv "a")
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") int,cz) Nothing))
        (SSeq annz
          (SInst annz "X" (int,cz)
            (SVar annz "fff" (TFunc FuncGlobal int int,cz)
              (Just $ EFunc annz (TFunc FuncGlobal int int,cz) (EVar annz "x")
                (SRet annz (ECons annz ["Int","1"])))))
          (SRet annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"]))))))
      `shouldBe` []
