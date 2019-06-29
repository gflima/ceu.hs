module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

int  = TypeD ["Int"]     [] Type0
int1 = TypeD ["Int","1"] [] Type0
int2 = TypeD ["Int","2"] [] Type0

bool  = TypeD ["Bool"]         [] Type0
boolf = TypeD ["Bool","False"] [] Type0
boolt = TypeD ["Bool","True"]  [] Type0

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
      int `supOf` TypeB       `shouldBe` (True,  TypeB,       [])
    it "BOT > Int" $
      TypeB       `supOf` int `shouldBe` (False, TypeB,       [])
    it "a > Int" $
      TypeV "a" `supOf` int `shouldBe` (True,  int, [("a",int,SUP)])
    it "a > b" $
      TypeV "a" `supOf` TypeV "b" `shouldBe` (True,TypeV "b",[("a",TypeV "b",SUP),("b",TypeV "a",SUB)])
    it "b > b" $
      TypeV "b" `supOf` TypeV "b" `shouldBe` (True,TypeV "b",[("b",TypeV "b",SUP),("b",TypeV "b",SUB)])

  describe "relates_" $ do

    it "b > b" $
      relates_ SUP (TypeV "b") (TypeV "b")
      `shouldBe` Right (TypeV "b",[("b",TypeV "b")])

    it "(a -> a) > (Int -> Int)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (int) (int))
      `shouldBe` Right ((TypeF (int) (int)), [("a", int)])

    it "(a -> b) > (A -> B)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "b")) (TypeF (TypeD ["A"] [] Type0) (TypeD ["B"] [] Type0))
      `shouldBe` Right ((TypeF (TypeD ["A"] [] Type0) (TypeD ["B"] [] Type0)), [("a", TypeD ["A"] [] Type0), ("b", TypeD ["B"] [] Type0)])

    it "(a -> a) > (Int -> ())" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (int) Type0)
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambiguous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(int),Type0])
      `shouldBe` Right (TypeN [int,Type0],[("a",int),("b",Type0)])

    it "(a,b,c) /> (Int,())" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b"),(TypeV "c")]) (TypeN [(int),Type0])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates_ SUP (TypeN [(TypeV "a"),(TypeV "b")]) (TypeN [(int),Type0,(int)])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates_ SUP (TypeF (TypeV "a") (TypeV "a")) (TypeF (int) (int1))
      `shouldBe` Right (TypeF (int) (int1),[("a",int)])

    it "(Int -> Int.1) > (a -> a)" $
      relates_ SUP (TypeF (int) (int1)) (TypeF (TypeV "a") (TypeV "a"))
      `shouldBe` Left ["types do not match : expected '(Int -> Int.1)' : found '(a -> a)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates_ SUP (TypeF (int) (int)) (TypeF (int1) (int))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(Int.1 -> Int) > (a -> a)" $
      relates_ SUP (TypeF (int1) (int)) (TypeF (TypeV "a") (TypeV "a"))
      `shouldBe` Right (TypeF (TypeV "a") (TypeV "a"),[("a",int)])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates_ SUP (TypeF (boolt) (bool)) (TypeF (bool) (bool))
      `shouldBe` Right (TypeF (bool) (bool),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates_ SUP (TypeF (boolt) (bool)) (TypeF (bool) (boolt))
      `shouldBe` Right (TypeF (bool) (boolt),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [TypeD ["X"] [] Type0, TypeD ["X","A"] [] Type0])
             Type0)
      `shouldBe` Right (TypeF (TypeN [TypeD ["X"] [] Type0,TypeD ["X","A"] [] Type0]) Type0,[("a",TypeD ["X","A"] [] Type0)])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             Type0)
      (TypeF (TypeN [TypeD ["Y"] [] Type0, TypeD ["X","A"] [] Type0])
             Type0)
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambiguous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a)->(a,a)) SUP ((X,X.A)->(X.A,X.A.B)" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [TypeD ["X"] [] Type0,     TypeD ["X","A"] [] Type0])
             (TypeN [TypeD ["X","A"] [] Type0, TypeD ["X","A","B"] [] Type0]))
      `shouldBe` Right (TypeF (TypeN [TypeD ["X"] [] Type0,TypeD ["X","A"] [] Type0]) (TypeN [TypeD ["X","A"] [] Type0,TypeD ["X","A","B"] [] Type0]),[("a",TypeD ["X","A"] [] Type0)])

    it "((X,X.A)->(X.A,X.A.B) SUP ((a,a)->(a,a))" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X"] [] Type0,     TypeD ["X","A"] [] Type0])
             (TypeN [TypeD ["X","A"] [] Type0, TypeD ["X","A","B"] [] Type0]))
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '((X,X.A) -> (X.A,X.A.B))' : found '((a,a) -> (a,a))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates_ SUP
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      (TypeF (TypeN [TypeD ["X"] [] Type0, TypeD ["X","A"] [] Type0])
             (TypeN [TypeD ["X"] [] Type0, TypeD ["X","A","B"] [] Type0]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A' should be supertype of 'X'"]

    it "(True,False)->() > (a,a)->()" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X","Bool","True"] [] Type0, TypeD ["X","Bool","False"] [] Type0]) Type0)
      (TypeF (TypeN [TypeV "a",                 TypeV "a"])                  Type0)
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) Type0,[("a",TypeD ["X","Bool"] [] Type0)])

    it "()->(True,False) SUP ()->(a,a)" $
      relates_ SUP
      (TypeF Type0 (TypeN [TypeD ["X","Bool","True"] [] Type0, TypeD ["X","Bool","False"] [] Type0]))
      (TypeF Type0 (TypeN [TypeV "a",                 TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '(() -> (X.Bool.True,X.Bool.False))' : found '(() -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->(True,False) SUP (a,a)->(a,a)" $
      relates_ SUP
      (TypeF (TypeN [TypeD ["X","Bool","True"] [] Type0, TypeD ["X","Bool","False"] [] Type0])
             (TypeN [TypeD ["X","Bool","True"] [] Type0, TypeD ["X","Bool","False"] [] Type0]))
      (TypeF (TypeN [TypeV "a", TypeV "a"])
             (TypeN [TypeV "a", TypeV "a"]))
      `shouldBe` Left ["types do not match : expected '((X.Bool.True,X.Bool.False) -> (X.Bool.True,X.Bool.False))' : found '((a,a) -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False', 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->top SUP (a,a)->a" $
      relates_ SUP
      (TypeF (TypeN [boolt, boolf]) TypeT)
      (TypeF (TypeN [TypeV "a",             TypeV "a"])              (TypeV "a"))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (TypeV "a"),[("a",bool)])

    it "((1,2),(1,1))->? SUP (Int,Int)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [int1,int2],
                TypeN [int1,int1]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeN [int,int],
                TypeN [int,int]
              ])
              (bool))
      `shouldBe` Right (TypeF (TypeN [TypeN [int,int],TypeN [int,int]]) (bool),[("?",bool)])

    it "((1,2),(1,1))->? SUP (a,a)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [int1,int2],
                TypeN [int1,int1]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeV "a",
                TypeV "a"
              ])
              (bool))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),[("?",bool),("a",TypeN [int1,int])])

    it "((1,2),(1,1))->? SUB (a,a)->Bool" $
      relates_ SUP
        (TypeF (TypeN [
                TypeN [int1,int2],
                TypeN [int1,int1]
              ])
              (TypeV "?"))
        (TypeF (TypeN [
                TypeV "a",
                TypeV "a"
              ])
              (bool))
      `shouldBe` Right (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),[("?",bool),("a",TypeN [int1,int])])

    it "(a,a) > (370,10)" $
      relates_ SUP
        (TypeN [TypeV "a",                   TypeV "a"])
        (TypeN [TypeD ["Int","370"] [] Type0,TypeD ["Int","10"] [] Type0])
      `shouldBe` Right (TypeN [TypeD ["Int","370"] [] Type0,TypeD ["Int","10"] [] Type0],[("a",TypeD ["Int"] [] Type0)])

    it "(a,a) > (X 370,X 10)" $
      relates_ SUP
        (TypeN [TypeV "a",                                     TypeV "a"])
        (TypeN [TypeD ["X"] [] $ TypeD ["Int","370"] [] Type0, TypeD ["X"] [] $ TypeD ["Int","10"] [] Type0])
      `shouldBe` Right (TypeN [TypeD ["X"] [] (TypeD ["Int","370"] [] Type0),TypeD ["X"] [] (TypeD ["Int","10"] [] Type0)],[("a",TypeD ["X"] [] (TypeD ["Int"] [] Type0))])

    it "Int > a" $
      supOf (TypeD ["Int"] [] Type0) (TypeV "a")
      `shouldBe` (True,TypeD ["Int"] [] Type0,[("a",TypeD ["Int"] [] Type0,SUB)])

    it "[I] > [a]" $
      supOf
        (TypeN [TypeD ["Int"] [] Type0]) (TypeN [TypeV "a"])
      `shouldBe` (True,TypeN [TypeD ["Int"] [] Type0],[("a",TypeD ["Int"] [] Type0,SUB)])

    it "P I > P a" $
      supOf
        (TypeD ["Pair"] [TypeD ["Int"] [] Type0] (TypeN [TypeD ["Int"] [] Type0]))
        (TypeD ["Pair"] [TypeV "a"]              (TypeN [TypeV "a"]))
      `shouldBe` (True,TypeD ["Pair"] [TypeD ["Int"] [] Type0] (TypeN [TypeD ["Int"] [] Type0]),[("a",TypeD ["Int"] [] Type0,SUB)])

    it "P I I > P a a" $
      supOf
        (TypeD ["Pair"] [TypeD ["Int"] [] Type0,TypeD ["Int"] [] Type0] (TypeN [TypeD ["Int"] [] Type0,TypeD ["Int"] [] Type0]))
        (TypeD ["Pair"] [TypeV "a",TypeV "b"] (TypeN [TypeV "a",TypeV "b"]))
      `shouldBe` (True,TypeD ["Pair"] [TypeD ["Int"] [] Type0,TypeD ["Int"] [] Type0] (TypeN [TypeD ["Int"] [] Type0,TypeD ["Int"] [] Type0]),[("a",TypeD ["Int"] [] Type0,SUB),("b",TypeD ["Int"] [] Type0,SUB)])

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TypeF TypeB TypeT `isSupOf_` TypeF TypeB TypeT
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TypeF TypeB TypeT `isSubOf_` TypeF TypeB TypeT
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TypeF TypeB TypeT `isSupOf_` TypeF TypeB TypeB
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TypeF TypeT TypeT `isSupOf_` TypeF TypeB TypeB
      `shouldBe` False

    it "top > Int" $
      TypeT `isSupOf_` (int)
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TypeF Type0 TypeT `isSupOf_` TypeF Type0 (int)
      `shouldBe` True

    it "Bool > Bool.True" $
      (bool `isSupOf_` boolt)
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",TypeD ["A"] [] Type0), ("b",TypeD ["B"] [] Type0)] (TypeD ["A"] [] Type0)
      `shouldBe` (TypeD ["A"] [] Type0)

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",TypeD ["A"] [] Type0), ("b",TypeD ["B"] [] Type0)] (TypeN [TypeV "a", TypeV "b"])
      `shouldBe` (TypeN [TypeD ["A"] [] Type0, TypeD ["B"] [] Type0])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",TypeD ["A"] [] Type0), ("b",TypeD ["B"] [] Type0)] (TypeF (TypeV "a") (TypeD ["C"] [] Type0))
      `shouldBe` (TypeF (TypeD ["A"] [] Type0) (TypeD ["C"] [] Type0))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (int) (int, int)
      `shouldBe` (int)

    it "Int : (a ~ Int) ~> Int" $
      inst' (int) (TypeV "a", int)
      `shouldBe` (int)

    it "a : (a ~ Int) ~> Int" $
      inst' (TypeV "a") (TypeV "a", int)
      `shouldBe` (int)

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [int,TypeV "a"], TypeN [int,int])
      `shouldBe` (int)

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",int], TypeN [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [int,bool])
      `shouldBe` TypeT

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "b"], TypeN [int,bool])
      `shouldBe` (int)

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TypeV "b") (TypeN [TypeV "a",TypeV "b"], TypeN [int,bool])
      `shouldBe` (bool)

  describe "comPre" $ do

    it "[A.1,A.1]" $
      comPre [TypeD ["A","1"] [] Type0, TypeD ["A","1"] [] Type0]
      `shouldBe` Just (TypeD ["A","1"] [] Type0)

    it "[A.1,A.2]" $
      comPre [TypeD ["A","1"] [] Type0, TypeD ["A","2"] [] Type0]
      `shouldBe` Just (TypeD ["A"] [] Type0)

    it "[A.1,A.2,a]" $
      comPre [TypeD ["A","1"] [] Type0, TypeD ["A","2"] [] Type0, TypeV "a"]
      `shouldBe` Just (TypeD ["A"] [] Type0)

    it "[A.1,A.2,a,(A.1,a),(A.2,a)]" $
      comPre [TypeD ["A","1"] [] Type0, TypeD ["A","2"] [] Type0, TypeV "a",
              TypeN [TypeD ["A","1"] [] Type0, TypeV "a"], TypeN [TypeD ["A","2"] [] Type0, TypeV "a"] ]
      `shouldBe` Just (TypeD ["A"] [] Type0)

    it "[(A.1->A.2), (A.2->a)]" $
      comPre [TypeF (TypeD ["A","1"] [] Type0) (TypeD ["A","2"] [] Type0),
              TypeF (TypeD ["A","2"] [] Type0) (TypeV "a")]
      `shouldBe` Just (TypeF (TypeD ["A"] [] Type0) (TypeD ["A","2"] [] Type0))

    it "[a,(A.1,a),(A.2,a)]" $
      comPre [ TypeV "a",
               TypeN [TypeD ["A","1"] [] Type0, TypeV "a"],
               TypeN [TypeD ["A","2"] [] Type0, TypeV "a"] ]
      `shouldBe` Just (TypeN [TypeD ["A"] [] Type0,TypeV "a"])

    it "[ [True,False] ]" $
      comPre [TypeN [boolt,boolf]]
      `shouldBe` Just (TypeN [boolt,boolf])

{-
    it "OK: [ [True,False], [True] ]" $ -- arity mismatch
      comPre [ TypeN [boolt,boolf],
               TypeN [boolt] ]
      `shouldBe` Just (TypeN [boolt,boolf])
-}

  describe "sort" $ do

    it "(Bool,Bool) <= Bool" $
      TypeN [TypeD ["Bool"] [] Type0, TypeD ["Bool"] [] Type0] <= TypeD ["Bool"] [] Type0
      `shouldBe` False
    it "Bool <= (Bool,Bool)" $
      TypeD ["Bool"] [] Type0 <= TypeN [TypeD ["Bool"] [] Type0, TypeD ["Bool"] [] Type0]
      `shouldBe` True
    it "((Int,(Bool,Int)) <= (Bool,Int)" $
      TypeN [int, TypeN [bool,int]] <= TypeN [bool, int]
      `shouldBe` False
    it "(Bool,Int) <= ((Int,(Bool,Int))" $
      TypeN [bool, int] <= TypeN [int, TypeN [bool,int]]
      `shouldBe` True
    it "[Bool,Int] <= [Int,(Int,Int)]" $
      TypeN [bool, int] <= TypeN [int, TypeN [int,int]]
      `shouldBe` True
    it "list" $
      sort' [
        [TypeN [TypeD ["Bool"] [] Type0,TypeD ["Bool"] [] Type0],TypeN [TypeD ["Bool"] [] Type0,TypeD ["Int"] [] Type0]],
        [TypeD ["Int"] [] Type0,TypeN [TypeD ["Bool"] [] Type0,TypeD ["Int"] [] Type0]]
       ]
      `shouldBe` [[TypeD ["Int"] [] Type0,TypeN [TypeD ["Bool"] [] Type0,TypeD ["Int"] [] Type0]],[TypeN [TypeD ["Bool"] [] Type0,TypeD ["Bool"] [] Type0],TypeN [TypeD ["Bool"] [] Type0,TypeD ["Int"] [] Type0]]]
    it "list" $
      sort' [
        [TypeD ["Int"]  [] Type0,TypeN [TypeD ["Int"]  [] Type0,TypeD ["Int"] [] Type0]],
        [TypeD ["Int"]  [] Type0,TypeD ["Int"] [] Type0]
       ]
      `shouldBe` [
        [TypeD ["Int"]  [] Type0,TypeD ["Int"] [] Type0],
        [TypeD ["Int"]  [] Type0,TypeN [TypeD ["Int"]  [] Type0,TypeD ["Int"] [] Type0]]
       ]

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates_ SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TypeT
