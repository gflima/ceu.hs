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
      `shouldBe` ["interface 'F3able' is not declared"]

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

{-
    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff1" (annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz) Map.empty
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff1" (annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff2" (annz,"fff2",(TFunc FuncGlobal (TData False ["A"] []) TUnit,cz),True))
          (func "fff2" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz))))))))
      `shouldBe` ["missing instance of 'fff1'","unexpected instance of 'fff2'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff1" (annz,"fff1",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff1" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz) Map.empty
          (SSeq annz
            (SNop annz)
            (SNop annz)))))))
      `shouldBe` ["missing instance of 'fff1'"]

    it "A ; Xable a ; inst Xable A ; ()/=Int" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TData False ["A"] []) (int),cz),True))
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) (int),cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected '(a -> ())' : found '(A -> Int)'"]

    it "A ; Xable a ; inst X A" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "X" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (int) TUnit,cz),True))
          (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["constraint 'X' is not declared"]

    it "A ; Xable a ; inst Xable A ; a/=A" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
          (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)        -- a
        (SInst annz "Xable" (TData False ["A"] [],cz)                          -- A
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (int) TUnit,cz), True))
          (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)  -- Int
            (SSeq annz
              (SNop annz)
              (SNop annz)))))))))
      `shouldBe` ["types do not match : expected 'A' : found 'Int'"]

    it "A ; Xable.fff(a) ; inst Xable A ; fff(A)" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TData False ["A"] []) TUnit,cz),True))
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A"]))))))))))
      `shouldBe` []

    it "Int ; A ; Xable a ; inst Xable A ; fff 1" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable")),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz), True))
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))))))))))
      --`shouldBe` ["types do not match : expected '(Int.1 -> ?)' : found '(A -> ())'"]
      `shouldBe` ["variable 'fff' has no associated instance for '(Int -> ?)'"]

    it "Int ; Bool ; Equalable a ; eq 1 Bool" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz bool Nothing TUnit cz False
        (SClass annz "Equalable" (cv "a") (Map.singleton "eq" (annz,"eq",(TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz),False))
        (SVar annz "eq" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz)
        (SCall annz (ECall annz (EVar annz "eq") (ETuple annz [(ECons annz ["Bool"]),(ECons annz ["Int","1"])]))))))))
      `shouldBe` ["types do not match : expected '((Bool,Int) -> ?)' : found '((a,a) -> Bool)'",
                  "ambiguous instances for 'a' : 'Bool', 'Int'"]

    it "Int ; Bool ; Xable a ; inst Xable Bool/Int ; fff 1 ; fff Bool" $
      (fst $ TypeSys.go
        (SData annz int Nothing TUnit cz False
        (SData annz bool Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (bool,cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (bool) TUnit,cz), True))
          (func "$fff$(Bool -> ())$" (TFunc FuncGlobal (bool) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (int,cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (int) TUnit,cz), True))
                (func "$fff$(Int -> ())$" (TFunc FuncGlobal (int) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SSeq annz
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Int","1"])))
                      (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["Bool"])))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["Int"] [] [] TUnit (SData annz Nothing ["Bool"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(Bool -> ())" (TFunc FuncGlobal (TData False ["Bool"]) TUnit) (SVar annz "fff$(Int -> ())" (TFunc FuncGlobal (TData False ["Int"]) TUnit) (SSeq annz (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["Int"]) TUnit,[]}) "fff$(Int -> ())") (ECons (annz {typec = (TData False ["Int","1"],[]}) ["Int","1"]))) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["Bool"]) TUnit,[]}) "fff$(Bool -> ())") (ECons (annz {typec = (TData False ["Bool"],[]}) ["Bool"] (EUnit (annz {typec = (TUnit,[]})))))))))))

    it "A ; A.B ; Xable a ; inst Xable A ; fff A.B (must use A.fff)" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz True
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz), True))
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"])))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit (SData annz Nothing ["A","B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc FuncGlobal (TData False ["A"]) TUnit) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["A"]) TUnit,[]}) "fff$(A -> ())") (ECons (annz {typec = (TData False ["A","B"],[]}) ["A","B"] (EUnit (annz {typec = (TUnit,[]})))))))))

    it "A ; A.B ; Xable a ; inst Xable A/A.B ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz True
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz), True))
          (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData False ["A","B"] [],cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz), True))
                (func "$fff$((A,B) -> ())$" (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["A"] [] [] TUnit (SData annz Nothing ["A","B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" ["Xable"]) TUnit) (SVar annz "fff$(A -> ())" (TFunc FuncGlobal (TData False ["A"]) TUnit) (SVar annz "fff$(A.B -> ())" (TFunc FuncGlobal (TData False ["A","B"]) TUnit) (SCall annz (ECall (annz {typec = (TUnit,[]}) (EVar (annz {typec = (TFunc FuncGlobal (TData False ["A","B"]) TUnit,[]}) "fff$(A.B -> ())") (ECons (annz {typec = (TData False ["A","B"],[]}) ["A","B"] (EUnit (annz {typec = (TUnit,[]}))))))))))

    it "TODO: A ; A.B ; Xable a ; inst Xable A.B/A ; fff A.B ; (must use A.B.fff)" $
      (fst $ TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SData annz (TData False ["A","B"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit,cz)
        (SInst annz "Xable" (TData False ["A","B"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz), True))
          (func "$fff$((A,B) -> ())$" (TFunc FuncGlobal (TData False ["A","B"] []) TUnit,cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "Xable" (TData False ["A"] [],cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz), True))
                (func "$fff$(A -> ())$" (TFunc FuncGlobal (TData False ["A"] []) TUnit,cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (ECons annz ["A","B"]))))))))))))))
      `shouldBe` ["TODO: sort by subtyping relation"]

  describe "return-data polymorphism" $ do

    it "B ; X.f:()->b ; inst B.f:()->B ; f()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["B"] []) Nothing TUnit cz False
        (SClass annz "X" (cv "b") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal TUnit (TVar False "b"),cz),False))
        (SVar annz "fff" (TFunc FuncGlobal TUnit (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal TUnit (TData False ["B"] []),cz), True))
          (func "$fff$(() -> B)$" (TFunc FuncGlobal TUnit (TData False ["B"] []),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal TUnit (TVar False "b" ["X"])) (SVar annz "fff$(() -> B)" (TFunc FuncGlobal TUnit (TData False ["B"])) (SCall annz (ECall (annz {typec = (TData False ["B"],[]}) (EVar (annz {typec = (TFunc FuncGlobal TUnit (TData False ["B"]),[]}) "fff$(() -> B)") (EUnit (annz {typec = (TUnit,[]})))))))

    it "B ; X.f:a->b ; inst B.f:a->B ; f()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["B"] []) Nothing TUnit cz False
        (SClass annz "X" (cv "b") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B"] []),cz), True))
          (func "$fff$(a -> B)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B"] []),cz)
            (SSeq annz
              (SNop annz)
              (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))
      `shouldBe` [] --,SData annz Nothing ["B"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B"])) (SCall annz (ECall (annz {typec = (TData False ["B"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B"]),[]}) "fff$(a -> B)") (EUnit (annz {typec = (TUnit,[]})))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; f()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["B1"] []) Nothing TUnit cz False
        (SData annz (TData False ["B2"] []) Nothing TUnit cz False
        (SClass annz "X" (cv "b") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz), True))
          (func "$fff$(a -> B)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [],cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz), True))
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
                  (SSeq annz
                    (SNop annz)
                    (SCall annz (ECall annz (EVar annz "fff") (EUnit annz))))))))))))))
                  -- the problem is that SCall accept any return data
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SCall annz (ECall (annz {typec = (TData False ["B2"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {typec = (TUnit,[]})))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b1=f()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["B1"] []) Nothing TUnit cz False
        (SData annz (TData False ["B2"] []) Nothing TUnit cz False
        (SClass annz "X" (cv "b") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz), True))
          (func "$fff$(a -> B1)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [],cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz), True))
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b1" (TData False ["B1"] [],cz)
                    (mmm annz False (EVar annz "b1")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SVar annz "b1" (TData False ["B1"]) (mmm annz False (EVar annz "b1") (ECall (annz {typec = (TData False ["B1"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"]),[]}) "fff$(a -> B1)") (EUnit (annz {typec = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

    it "B1 ; B2 ; X.f:a->b ; inst B1.f:a->B1 ; inst B2.f:a->B2 ; b2=f()" $
      (fst $ TypeSys.go
        (SData annz (TData False ["B1"] []) Nothing TUnit cz False
        (SData annz (TData False ["B2"] []) Nothing TUnit cz False
        (SClass annz "X" (cv "b") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (TVar False "b"),cz)
        (SInst annz "X" (TData False ["B1"] [],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz), True))
          (func "$fff$(a -> B1)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B1"] []),cz)
            (SSeq annz
              (SNop annz)
              (SInst annz "X" (TData False ["B2"] [],cz)
                (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz), True))
                (func "$fff$(a -> B2)$" (TFunc FuncGlobal (TVar False "a") (TData False ["B2"] []),cz)
                  (SSeq annz
                    (SNop annz)
                    (SVar annz "b2" (TData False ["B2"] [],cz)
                    (mmm annz False (EVar annz "b2")
                      (ECall annz (EVar annz "fff") (EUnit annz)) (SNop annz) (SNop annz))))))))))))))
      `shouldBe` [] --,SData annz Nothing ["B1"] [] [] TUnit (SData annz Nothing ["B2"] [] [] TUnit (SVar annz "fff" (TFunc FuncGlobal (TVar False "a" []) (TVar False "b" ["X"])) (SVar annz "fff$(a -> B1)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B1"])) (SVar annz "fff$(a -> B2)" (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"])) (SVar annz "b2" (TData False ["B2"]) (mmm annz False (EVar annz "b2") (ECall (annz {typec = (TData False ["B2"],[]}) (EVar (annz {typec = (TFunc FuncGlobal (TVar False "a" []) (TData False ["B2"]),[]}) "fff$(a -> B2)") (EUnit (annz {typec = (TUnit,[]}))) (SNop annz) (SNop annz))))))))

    it "Int ; X a ; inst X Int ; return fff 1" $
      (fst $ TypeSys.go $ Simplify.go
        (SData annz int Nothing TUnit cz False
        (SClass annz "X" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") (int),cvc ("a","X")),False))
            (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") (int),cvc ("a","X"))
        (SInst annz "X" (int,cz)
            (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (int) (int),cz),True))
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

    it "class/inst/0" $ do
      (snd.compile)
        (SInst annz "F3able" (int,cz)
          (SFunc annz "f3" (TFunc FuncGlobal (TVar False "Int") (int),cz) (EAny annz)
            (SRet annz (ECons annz ["Int","10"]))))
      `shouldBe`
        (SVarS annz "$f3$(Int -> Int)$" (TFunc FuncGlobal (TVar False "Int") (int),cz) Nothing
          (set' annz False (EVar annz "$f3$(Int -> Int)$")
            (EFunc' annz (TFunc FuncGlobal (TVar False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"])))
            (SNop annz) (SRet annz (EError annz (-2)))))

    it "class/inst/1" $ do
      (snd.compile) (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SVar annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cz) Nothing))
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc FuncGlobal (TVar False "Int") (int),cz) (EAny annz)
                    (SRet annz (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClassS annz "F3able" (cv "a")
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")),False))
        (SVarS annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")) Nothing
        (SInstS annz "F3able" (int,cz)
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "Int") (int),cz),True))
        (SVarS annz "$f3$(Int -> Int)$" (TFunc FuncGlobal (TVar False "Int") (int),cz) Nothing
            (set' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc' annz (TFunc FuncGlobal (TVar False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"]))) (SNop annz) (SRet annz (EError annz (-2))))))))

    it "class/inst/2" $ do
      (snd.compile) (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SVar annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cz) Nothing))
              (SSeq annz
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc FuncGlobal (TVar False "Int") (int),cz) (EAny annz)
                    (SRet annz (ECons annz ["Int","10"]))))
              (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClassS annz "F3able" (cv "a")
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")),False))
        (SVarS annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")) Nothing
        (SInstS annz "F3able" (int,cz)
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "Int") (int),cz),True))
        (SVarS annz "$f3$(Int -> Int)$" (TFunc FuncGlobal (TVar False "Int") (int),cz) Nothing
          (SSeq annz
            (set' annz False (EVar annz "$f3$(Int -> Int)$") (EFunc' annz (TFunc FuncGlobal (TVar False "Int") (int),cz) (SRet annz (ECons annz ["Int","10"])))
              (SNop annz)
              (SRet annz (EError annz (-2))))
            (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))))))
    it "class/inst/3" $ do
      (snd.compile) (SSeq annz
                (SClass annz "F3able" (cv "a")
                  (SSeq annz
                  (SSeq annz
                  (SVar annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cz) Nothing)
                  (SNop annz))
                  (SNop annz)))
                (SSeq annz
                (SInst annz "F3able" (int,cz)
                  (SFunc annz "f3" (TFunc FuncGlobal (TVar False "Int") (int),cz) (EAny annz)
                    (SSeq annz
                    (SSeq annz
                    (SVar annz "v" (TVar False "Int",cz) Nothing)
                    (SNop annz))
                    (SSeq annz
                    (SSet annz True False (EVar annz "v") (EArg annz))
                    (SRet annz (EVar annz "v"))))))
                (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"])))))
      `shouldBe`
        (SClassS annz "F3able" (cv "a")
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")),False))
        (SVarS annz "f3" (TFunc FuncGlobal (TVar False "a") (int),cvc("a","F3able")) Nothing
        (SSeq annz
        (SNop annz)
        (SSeq annz
        (SNop annz)
        (SInstS annz "F3able" (int,cz)
          (singleton "f3" (annz,"f3",(TFunc FuncGlobal (TVar False "Int") (int),cz),True))
          (SVarS annz "$f3$(Int -> Int)$" (TFunc FuncGlobal (TVar False "Int") (int),cz) Nothing
          (SSeq annz
            (set' annz False (EVar annz "$f3$(Int -> Int)$")
              (EFunc' annz (TFunc FuncGlobal (TVar False "Int") (int),cz)
                (SVarS annz "v" (TVar False "Int",cz) Nothing
                (SSeq annz
                (SNop annz)
                (SSeq annz
                  (set' annz False (EVar annz "v") (EArg annz)
                    (SNop annz)
                    (SRet annz (EError annz (-2))))
                  (SRet annz (EVar annz "v"))))))
              (SNop annz)
              (SRet annz (EError annz (-2))))
            (SRet annz (ECall annz (EVar annz "f3") (ECons annz ["Int","10"]))))))))))

    it "Xxx.Yyy" $
      (snd.compile) (SSeq annz (SData annz int                            Nothing TUnit (fromList []) False)
              (SSeq annz (SData annz (TData False ["Xxx"]       []) Nothing int   (fromList []) True)
              (SSeq annz (SData annz (TData False ["Xxx","Yyy"] []) Nothing int   (fromList []) False)
              (SSeq annz
              (SSeq annz (SVar annz "y" (TData False ["Xxx","Yyy"] [],fromList []) Nothing)
                        (SNop annz))
                        (SSet annz True False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])))))))
      `shouldBe`
        SDataS annz (TData False ["Int"] []) Nothing TUnit (fromList []) False (SDataS annz (TData False ["Xxx"] []) Nothing (TData False ["Int"] []) (fromList []) True (SVarS annz "Xxx._1" (TFunc FuncGlobal (TData False ["Xxx"] []) (TData False ["Int"] []),fromList []) Nothing (SMatch  annz True False (EFunc' annz (TFunc FuncGlobal (TData False ["Xxx"] []) (TData False ["Int"] []),fromList []) (SVarS annz "_ret" (TData False ["Int"] [],fromList []) Nothing (SMatch  annz True False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx"]) (EVar annz "_ret"),SRet annz (EVar annz "_ret"))]))) [(SNop annz,EVar annz "Xxx._1",SDataS annz (TData False ["Xxx","Yyy"] []) Nothing (TTuple [TData False ["Int"] [],TData False ["Int"] []]) (fromList []) False (SVarS annz "Xxx.Yyy._2" (TFunc FuncGlobal (TData False ["Xxx","Yyy"] []) (TData False ["Int"] []),fromList []) Nothing (SMatch  annz True False (EFunc' annz (TFunc FuncGlobal (TData False ["Xxx","Yyy"] []) (TData False ["Int"] []),fromList []) (SVarS annz "_ret" (TData False ["Int"] [],fromList []) Nothing (SMatch  annz True False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [EAny annz,EVar annz "_ret"]),SRet annz (EVar annz "_ret"))]))) [(SNop annz,EVar annz "Xxx.Yyy._2",SVarS annz "Xxx.Yyy._1" (TFunc FuncGlobal (TData False ["Xxx","Yyy"] []) (TData False ["Int"] []),fromList []) Nothing (SMatch  annz True False (EFunc' annz (TFunc FuncGlobal (TData False ["Xxx","Yyy"] []) (TData False ["Int"] []),fromList []) (SVarS annz "_ret" (TData False ["Int"] [],fromList []) Nothing (SMatch  annz True False (EArg annz) [(SNop annz,ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [EVar annz "_ret",EAny annz]),SRet annz (EVar annz "_ret"))]))) [(SNop annz,EVar annz "Xxx.Yyy._1",SVarS annz "y" (TData False ["Xxx","Yyy"] [],fromList []) Nothing (SSeq annz (SNop annz) (SMatch  annz True False (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"],ECons annz ["Int","2"]])) [(SNop annz,EVar annz "y",SNop annz)])))]))])))])))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SClass annz "Equalable" (cv "a") Map.empty
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool),cz)
        (SNop annz))))
      `shouldBe` ([],SData annz bool Nothing TUnit cz True (SVar annz "==" (TFunc FuncGlobal (TTuple [TVar False "a",TVar False "a"]) (bool),cz) (SNop annz)))

    it "Bool ; Equalable ; (==)" $
      TypeSys.go
        (SData annz bool Nothing TUnit cz True
        (SClass annz "Equalable" (cv "a") Map.empty
        (SVar annz "==" (TFunc FuncGlobal (TTuple [(TVar False "a"),(TVar False "a")]) (bool), cvc ("a","Equalable"))
        (SNop annz))))
      `shouldBe` ([],SData annz bool Nothing TUnit cz True (SNop annz))

    it "A ; Xable.fff(a) ; SInst Xable (A,A) ; fff(A,A)" $
      TypeSys.go
        (SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SClass annz "Xable" (cv "a") (Map.singleton "fff" (annz,"fff",(TFunc FuncGlobal (TVar False "a") TUnit,cz),False))
        (SVar annz "fff" (TFunc FuncGlobal (TVar False "a") TUnit, cvc ("a","Xable"))
        (SInst annz "Xable" (TTuple [TData False ["A"] [], TData False ["A"] []],cz)
          (Map.singleton "fff" (annz, "fff", (TFunc FuncGlobal (TTuple [TData False ["A"] [], TData False ["A"] []]) TUnit,cz), True))
          (func "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [], TData False ["A"] []]) TUnit,cz)
            (SCall annz (ECall annz (EVar annz "fff") (ETuple annz [(ECons annz ["A"]),(ECons annz ["A"])]))))))))
      `shouldBe` ([],
        SData annz (TData False ["A"] []) Nothing TUnit cz False
        (SVar annz "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [],TData False ["A"] []]) TUnit,cz)
        (SVar annz "$fff$((A,A) -> ())$" (TFunc FuncGlobal (TTuple [TData False ["A"] [],TData False ["A"] []]) TUnit,cz)
        (mmm annz False (EVar annz "$fff$((A,A) -> ())$")
          (EFunc (annz {typec = (TFunc FuncGlobal (TTuple [TData False ["A"] [],TData False ["A"] []]) TUnit,cz)}) (TFunc FuncGlobal (TTuple [TData False ["A"] [],TData False ["A"] []]) TUnit,cz) (EUnit annz) (SRet annz (EError annz 99)))
          (SCall annz
            (ECall (annz {typec = (TUnit,cz)})
              (EVar (annz {typec = (TFunc FuncGlobal (TTuple [TData False ["A"] [],TData False ["A"] []]) TUnit,cz)}) "fff")
              (ETuple
                (annz {typec = (TTuple [TData False ["A"] [],TData False ["A"] []],cz)}) [ECons (annz {typec = (TData False ["A"] [],cz)}) ["A"],ECons (annz {typec = (TData False ["A"] [],cz)}) ["A"]])))
          (SRet annz (EError annz 99))))))

-}
