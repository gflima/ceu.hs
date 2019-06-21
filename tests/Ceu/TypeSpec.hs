module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

{-
  describe "TODO:" $ do

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X.A,X.A.B)" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
            (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [TypeD ["X"],     TypeD ["X","A"]])
            (TypeN [TypeD ["X","A"], TypeD ["X","A","B"]]))
      `shouldBe` Right (TypeF (TypeN [TypeD ["X"],TypeD ["X","A"]]) (TypeN [TypeD ["X","A"],TypeD ["X","A","B"]]),[("a",TypeD ["X","A"])])
-}

  describe "supOf" $ do

    it "Int > BOT" $
      TypeD ["Int"] `supOf` TypeB       `shouldBe` (True,  TypeB,       [])
    it "BOT > Int" $
      TypeB       `supOf` TypeD ["Int"] `shouldBe` (False, TypeB,       [])
    it "a > Int" $
      TypeV "a" `supOf` TypeD ["Int"] `shouldBe` (True,  TypeD ["Int"], [("a",TypeD ["Int"],SUP)])
    it "a > b" $
      TypeV "a" `supOf` TypeV "b" `shouldBe` (True,TypeV "b",[("a",TypeV "b",SUP),("b",TypeV "a",SUB)])
    it "b > b" $
      TypeV "b" `supOf` TypeV "b" `shouldBe` (True,TypeV "b",[("b",TypeV "b",SUP),("b",TypeV "b",SUB)])

  describe "relates_" $ do

    it "b > b" $
      relates_ SUP (TypeV "b") (TypeV "b")
      `shouldBe` Right (TypeV "b",[("b",TypeV "b")])

    it "(a -> a) > (Int -> Int)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (TypeD ["Int"]) (TypeD ["Int"]))
      `shouldBe` Right ((TypeF (TypeD ["Int"]) (TypeD ["Int"])), [("a", TypeD ["Int"])])

    it "(a -> b) > (A -> B)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "b")) (TypeF (TypeD ["A"]) (TypeD ["B"]))
      `shouldBe` Right ((TypeF (TypeD ["A"]) (TypeD ["B"])), [("a", TypeD ["A"]), ("b", TypeD ["B"])])

    it "(a -> a) > (Int -> ())" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (TypeD ["Int"]) Type0)
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambigous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(TypeD ["Int"]),Type0])
      `shouldBe` Right (TypeN [TypeD ["Int"],Type0],[("a",TypeD ["Int"]),("b",Type0)])

    it "(a,b,c) /> (Int,())" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b"),(TypeV "c")]) (TypeN [(TypeD ["Int"]),Type0])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(TypeD ["Int"]),Type0,(TypeD ["Int"])])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (TypeD ["Int"]) (TypeD ["Int","1"]))
      `shouldBe` Right (TypeF (TypeD ["Int"]) (TypeD ["Int","1"]),[("a",TypeD ["Int"])])

    it "(Int -> Int.1) > (a -> a)" $
      relates_ SUP (TypeF (TypeD ["Int"]) (TypeD ["Int","1"])) (TypeF (TypeV "a") (TypeV "a"))
      `shouldBe` Left ["types do not match : expected '(Int -> Int.1)' : found '(a -> a)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates_ SUP (TypeF (TypeD ["Int"]) (TypeD ["Int"])) (TypeF (TypeD ["Int","1"]) (TypeD ["Int"]))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(Int.1 -> Int) > (a -> a)" $
      relates_ SUP (TypeF (TypeD ["Int","1"]) (TypeD ["Int"])) (TypeF (TypeV "a") (TypeV "a"))
      `shouldBe` Right (TypeF (TypeV "a") (TypeV "a"),[("a",TypeD ["Int"])])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates_ SUP (TypeF (TypeD ["Bool","True"]) (TypeD ["Bool"])) (TypeF (TypeD ["Bool"]) (TypeD ["Bool"]))
      `shouldBe` Right (TypeF (TypeD ["Bool"]) (TypeD ["Bool"]),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates_ SUP (TypeF (TypeD ["Bool","True"]) (TypeD ["Bool"])) (TypeF (TypeD ["Bool"]) (TypeD ["Bool","True"]))
      `shouldBe` Right (TypeF (TypeD ["Bool"]) (TypeD ["Bool","True"]),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [TypeD ["X"], TypeD ["X","A"]])
             Type0)
      `shouldBe` Right (TypeF (TypeN [TypeD ["X"],TypeD ["X","A"]]) Type0,[("a",TypeD ["X","A"])])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [TypeD ["Y"], TypeD ["X","A"]])
             Type0)
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambigous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a)->(a,a)) SUP ((X,X.A)->(X.A,X.A.B)" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [TypeD ["X"],     TypeD ["X","A"]])
             (TypeN [TypeD ["X","A"], TypeD ["X","A","B"]]))
      `shouldBe` Right (TypeF (TypeN [TypeD ["X"],TypeD ["X","A"]]) (TypeN [TypeD ["X","A"],TypeD ["X","A","B"]]),[("a",TypeD ["X","A"])])

    it "((X,X.A)->(X.A,X.A.B) SUP ((a,a)->(a,a))" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X"],     TypeD ["X","A"]])
             (TypeN [TypeD ["X","A"], TypeD ["X","A","B"]]))
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '((X,X.A) -> (X.A,X.A.B))' : found '((a,a) -> (a,a))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [TypeD ["X"], TypeD ["X","A"]])
             (TypeN [TypeD ["X"], TypeD ["X","A","B"]]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A' should be supertype of 'X'"]

    it "(True,False)->() > (a,a)->()" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X","Bool","True"], TypeD ["X","Bool","False"]]) Type0)
      (TypeF (TypeN [TypeV "a",                 TypeV "a"])                  Type0)
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) Type0,[("a",TypeD ["X","Bool"])])

    it "()->(True,False) SUP ()->(a,a)" $
      relates_ SUP
      (TypeF Type0 (TypeN [TypeD ["X","Bool","True"], TypeD ["X","Bool","False"]]))
      (TypeF Type0 (TypeN [TypeV "a",                 TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '(() -> (X.Bool.True,X.Bool.False))' : found '(() -> (a,a))'","ambigous instances for 'a' : 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->(True,False) SUP (a,a)->(a,a)" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X","Bool","True"], TypeD ["X","Bool","False"]])
             (TypeN [TypeD ["X","Bool","True"], TypeD ["X","Bool","False"]]))
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '((X.Bool.True,X.Bool.False) -> (X.Bool.True,X.Bool.False))' : found '((a,a) -> (a,a))'","ambigous instances for 'a' : 'X.Bool.True', 'X.Bool.False', 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->top SUP (a,a)->a" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["Bool","True"], TypeD ["Bool","False"]]) TypeT)
      (TypeF (TypeN [TypeV "a",             TypeV "a"])              (TypeV "a"))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeV "a"),[("a",TypeD ["Bool"])])

    it "((1,2),(1,1))->? SUP (Int,Int)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [TypeD ["Int","1"],TypeD ["Int","2"]],
                TypeN [TypeD ["Int","1"],TypeD ["Int","1"]]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeN [TypeD ["Int"],TypeD ["Int"]],
                TypeN [TypeD ["Int"],TypeD ["Int"]]
              ])
              (TypeD ["Bool"]))
      `shouldBe` Right (TypeF (TypeN [TypeN [TypeD ["Int"],TypeD ["Int"]],TypeN [TypeD ["Int"],TypeD ["Int"]]]) (TypeD ["Bool"]),[("?",TypeD ["Bool"])])

    it "((1,2),(1,1))->? SUP (a,a)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [TypeD ["Int","1"],TypeD ["Int","2"]],
                TypeN [TypeD ["Int","1"],TypeD ["Int","1"]]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeV "a",
                TypeV "a"
              ])
              (TypeD ["Bool"]))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeD ["Bool"]),[("?",TypeD ["Bool"]),("a",TypeN [TypeD ["Int","1"],TypeD ["Int"]])])

    it "((1,2),(1,1))->? SUB (a,a)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [TypeD ["Int","1"],TypeD ["Int","2"]],
                TypeN [TypeD ["Int","1"],TypeD ["Int","1"]]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeV "a",
                TypeV "a"
              ])
              (TypeD ["Bool"]))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeD ["Bool"]),[("?",TypeD ["Bool"]),("a",TypeN [TypeD ["Int","1"],TypeD ["Int"]])])

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TypeF TypeB TypeT `isSupOf_` TypeF TypeB TypeT
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TypeF TypeB TypeT `isSubOf` TypeF TypeB TypeT
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TypeF TypeB TypeT `isSupOf_` TypeF TypeB TypeB
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TypeF TypeT TypeT `isSupOf_` TypeF TypeB TypeB
      `shouldBe` False

    it "top > Int" $
      TypeT `isSupOf_` (TypeD ["Int"])
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TypeF Type0 TypeT `isSupOf_` TypeF Type0 (TypeD ["Int"])
      `shouldBe` True

    it "Bool > Bool.True" $
      (TypeD ["Bool"] `isSupOf_` TypeD ["Bool", "True"])
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",TypeD ["A"]), ("b",TypeD ["B"])] (TypeD ["A"])
      `shouldBe` (TypeD ["A"])

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",TypeD ["A"]), ("b",TypeD ["B"])] (TypeN [TypeV "a", TypeV "b"])
      `shouldBe` (TypeN [TypeD ["A"], TypeD ["B"]])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",TypeD ["A"]), ("b",TypeD ["B"])] (TypeF (TypeV "a") (TypeD ["C"]))
      `shouldBe` (TypeF (TypeD ["A"]) (TypeD ["C"]))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (TypeD ["Int"]) (TypeD ["Int"], TypeD ["Int"])
      `shouldBe` (TypeD ["Int"])

    it "Int : (a ~ Int) ~> Int" $
      inst' (TypeD ["Int"]) (TypeV "a", TypeD ["Int"])
      `shouldBe` (TypeD ["Int"])

    it "a : (a ~ Int) ~> Int" $
      inst' (TypeV "a") (TypeV "a", TypeD ["Int"])
      `shouldBe` (TypeD ["Int"])

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeD ["Int"],TypeV "a"], TypeN [TypeD ["Int"],TypeD ["Int"]])
      `shouldBe` (TypeD ["Int"])

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeD ["Int"]], TypeN [TypeD ["Int"],TypeD ["Int"]])
      `shouldBe` (TypeD ["Int"])

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [TypeD ["Int"],TypeD ["Int"]])
      `shouldBe` (TypeD ["Int"])

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [TypeD ["Int"],TypeD ["Bool"]])
      `shouldBe` TypeT

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "b"], TypeN [TypeD ["Int"],TypeD ["Bool"]])
      `shouldBe` (TypeD ["Int"])

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TypeV "b") (TypeN [TypeV "a",TypeV "b"], TypeN [TypeD ["Int"],TypeD ["Bool"]])
      `shouldBe` (TypeD ["Bool"])

  describe "comPre" $ do

    it "[A.1,A.1]" $
      comPre [TypeD ["A","1"], TypeD ["A","1"]]
      `shouldBe` Just (TypeD ["A","1"])

    it "[A.1,A.2]" $
      comPre [TypeD ["A","1"], TypeD ["A","2"]]
      `shouldBe` Just (TypeD ["A"])

    it "[A.1,A.2,a]" $
      comPre [TypeD ["A","1"], TypeD ["A","2"], TypeV "a"]
      `shouldBe` Just (TypeD ["A"])

    it "[A.1,A.2,a,(A.1,a),(A.2,a)]" $
      comPre [TypeD ["A","1"], TypeD ["A","2"], TypeV "a",
              TypeN [TypeD ["A","1"], TypeV "a"], TypeN [TypeD ["A","2"], TypeV "a"] ]
      `shouldBe` Just (TypeD ["A"])

    it "[(A.1->A.2), (A.2->a)]" $
      comPre [TypeF (TypeD ["A","1"]) (TypeD ["A","2"]),
              TypeF (TypeD ["A","2"]) (TypeV "a")]
      `shouldBe` Just (TypeF (TypeD ["A"]) (TypeD ["A","2"]))

    it "[a,(A.1,a),(A.2,a)]" $
      comPre [ TypeV "a",
               TypeN [TypeD ["A","1"], TypeV "a"],
               TypeN [TypeD ["A","2"], TypeV "a"] ]
      `shouldBe` Just (TypeN [TypeD ["A"],TypeV "a"])

    it "[ [True,False] ]" $
      comPre [TypeN [TypeD ["Bool","True"],TypeD ["Bool","False"]]]
      `shouldBe` Just (TypeN [TypeD ["Bool","True"],TypeD ["Bool","False"]])

    it "OK: [ [True,False], [True] ]" $ -- arity mismatch
      comPre [ TypeN [TypeD ["Bool","True"],TypeD ["Bool","False"]],
               TypeN [TypeD ["Bool","True"]] ]
      `shouldBe` Just (TypeN [TypeD ["Bool","True"],TypeD ["Bool","False"]])

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates_ SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TypeT
