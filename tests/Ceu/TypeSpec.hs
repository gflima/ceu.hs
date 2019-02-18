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
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
            (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [Type1 ["X"],     Type1 ["X","A"]])
            (TypeN [Type1 ["X","A"], Type1 ["X","A","B"]]))
      `shouldBe` Right (TypeF (TypeN [Type1 ["X"],Type1 ["X","A"]]) (TypeN [Type1 ["X","A"],Type1 ["X","A","B"]]),[("a",Type1 ["X","A"])])
-}

  describe "supOf" $ do

    it "Int > BOT" $
      Type1 ["Int"] `supOf` TypeB       `shouldBe` (True,  TypeB,       [])
    it "BOT > Int" $
      TypeB       `supOf` Type1 ["Int"] `shouldBe` (False, TypeB,       [])
    it "a > Int" $
      TypeV "a"   `supOf` Type1 ["Int"] `shouldBe` (True,  Type1 ["Int"], [("a",Type1 ["Int"],SUP)])
    it "a > b" $
      TypeV "a"   `supOf` TypeV "b"   `shouldBe` (True,TypeV "b",[("a",TypeV "b",SUP),("b",TypeV "a",SUB)])
    it "b > b" $
      TypeV "b"   `supOf` TypeV "b"   `shouldBe` (True,TypeV "b",[("b",TypeV "b",SUP),("b",TypeV "b",SUB)])

  describe "relates" $ do

    it "b > b" $
      relates SUP (TypeV "b") (TypeV "b")
      `shouldBe` Right (TypeV "b",[("b",TypeV "b")])

    it "(a -> a) > (Int -> Int)" $
      relates SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
      `shouldBe` Right ((TypeF (Type1 ["Int"]) (Type1 ["Int"])), [("a", Type1 ["Int"])])

    it "(a -> b) > (A -> B)" $
      relates SUP (TypeF (TypeV "a") (TypeV "b")) (TypeF (Type1 ["A"]) (Type1 ["B"]))
      `shouldBe` Right ((TypeF (Type1 ["A"]) (Type1 ["B"])), [("a", Type1 ["A"]), ("b", Type1 ["B"])])

    it "(a -> a) > (Int -> ())" $
      relates SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (Type1 ["Int"]) Type0)
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambigous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(Type1 ["Int"]),Type0])
      `shouldBe` Right (TypeN [Type1 ["Int"],Type0],[("a",Type1 ["Int"]),("b",Type0)])

    it "(a,b,c) /> (Int,())" $
      relates SUP (TypeN [(TypeV "a"),(TypeV "b"),(TypeV "c")]) (TypeN [(Type1 ["Int"]),Type0])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(Type1 ["Int"]),Type0,(Type1 ["Int"])])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (Type1 ["Int"]) (Type1 ["Int","1"]))
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> Int.1)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates SUP (TypeF (Type1 ["Int"]) (Type1 ["Int"])) (TypeF (Type1 ["Int","1"]) (Type1 ["Int"]))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(a -> a) > (Int.1 -> Int)" $
      relates SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (Type1 ["Int","1"]) (Type1 ["Int"]))
      `shouldBe` Right (TypeF (Type1 ["Int","1"]) (Type1 ["Int"]),[("a",Type1 ["Int"])])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates SUP (TypeF (Type1 ["Bool","True"]) (Type1 ["Bool"])) (TypeF (Type1 ["Bool"]) (Type1 ["Bool"]))
      `shouldBe` Right (TypeF (Type1 ["Bool"]) (Type1 ["Bool"]),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates SUP (TypeF (Type1 ["Bool","True"]) (Type1 ["Bool"])) (TypeF (Type1 ["Bool"]) (Type1 ["Bool","True"]))
      `shouldBe` Right (TypeF (Type1 ["Bool"]) (Type1 ["Bool","True"]),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [Type1 ["X"], Type1 ["X","A"]])
             Type0)
      `shouldBe` Right (TypeF (TypeN [Type1 ["X"],Type1 ["X","A"]]) Type0,[("a",Type1 ["X"])])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [Type1 ["Y"], Type1 ["X","A"]])
             Type0)
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambigous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X.A,X.A.B)" $
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [Type1 ["X"],     Type1 ["X","A"]])
             (TypeN [Type1 ["X","A"], Type1 ["X","A","B"]]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X.A,X.A.B))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [Type1 ["X"], Type1 ["X","A"]])
             (TypeN [Type1 ["X"], Type1 ["X","A","B"]]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "(a,a) -> () > (True,False) -> ()" $
      relates SUP
      (TypeF (TypeN [TypeV "a",                 TypeV "a"])                  Type0)
      (TypeF (TypeN [Type1 ["X","Bool","True"], Type1 ["X","Bool","False"]]) Type0)
      `shouldBe` Right (TypeF (TypeN [Type1 ["X","Bool","True"],Type1 ["X","Bool","False"]]) Type0,[("a",Type1 ["X","Bool"])])

    it "() -> (a,a) > () -> (True,False)" $
      relates SUP
      (TypeF Type0 (TypeN [TypeV "a",                 TypeV "a"]))
      (TypeF Type0 (TypeN [Type1 ["X","Bool","True"], Type1 ["X","Bool","False"]]))
      `shouldBe` Left ["TODO"]

    it "(a,a) -> (a,a) > (True,False) -> (True,False)" $
      relates SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [Type1 ["X","Bool","True"], Type1 ["X","Bool","False"]])
             (TypeN [Type1 ["X","Bool","True"], Type1 ["X","Bool","False"]]))
      `shouldBe` Left ["TODO"]

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TypeF TypeB TypeT `isSupOf` TypeF TypeB TypeT
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TypeF TypeB TypeT `isSubOf` TypeF TypeB TypeT
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TypeF TypeB TypeT `isSupOf` TypeF TypeB TypeB
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TypeF TypeT TypeT `isSupOf` TypeF TypeB TypeB
      `shouldBe` False

    it "top > Int" $
      TypeT `isSupOf` (Type1 ["Int"])
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TypeF Type0 TypeT `isSupOf` TypeF Type0 (Type1 ["Int"])
      `shouldBe` True

    it "Bool > Bool.True" $
      (Type1 ["Bool"] `isSupOf` Type1 ["Bool", "True"])
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",Type1 ["A"]), ("b",Type1 ["B"])] (Type1 ["A"])
      `shouldBe` (Type1 ["A"])

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",Type1 ["A"]), ("b",Type1 ["B"])] (TypeN [TypeV "a", TypeV "b"])
      `shouldBe` (TypeN [Type1 ["A"], Type1 ["B"]])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",Type1 ["A"]), ("b",Type1 ["B"])] (TypeF (TypeV "a") (Type1 ["C"]))
      `shouldBe` (TypeF (Type1 ["A"]) (Type1 ["C"]))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (Type1 ["Int"]) (Type1 ["Int"], Type1 ["Int"])
      `shouldBe` (Type1 ["Int"])

    it "Int : (a ~ Int) ~> Int" $
      inst' (Type1 ["Int"]) (TypeV "a", Type1 ["Int"])
      `shouldBe` (Type1 ["Int"])

    it "a : (a ~ Int) ~> Int" $
      inst' (TypeV "a") (TypeV "a", Type1 ["Int"])
      `shouldBe` (Type1 ["Int"])

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [Type1 ["Int"],TypeV "a"], TypeN [Type1 ["Int"],Type1 ["Int"]])
      `shouldBe` (Type1 ["Int"])

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",Type1 ["Int"]], TypeN [Type1 ["Int"],Type1 ["Int"]])
      `shouldBe` (Type1 ["Int"])

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [Type1 ["Int"],Type1 ["Int"]])
      `shouldBe` (Type1 ["Int"])

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [Type1 ["Int"],Type1 ["Bool"]])
      `shouldBe` TypeT

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "b"], TypeN [Type1 ["Int"],Type1 ["Bool"]])
      `shouldBe` (Type1 ["Int"])

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TypeV "b") (TypeN [TypeV "a",TypeV "b"], TypeN [Type1 ["Int"],Type1 ["Bool"]])
      `shouldBe` (Type1 ["Bool"])

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TypeT
