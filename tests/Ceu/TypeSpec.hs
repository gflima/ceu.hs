module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

int  = TData ["Int"]     [] TUnit
int1 = TData ["Int","1"] [] TUnit
int2 = TData ["Int","2"] [] TUnit

bool  = TData ["Bool"]         [] TUnit
boolf = TData ["Bool","False"] [] TUnit
boolt = TData ["Bool","True"]  [] TUnit

spec :: Spec
spec = do

{-
  describe "TODO:" $ do

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X.A,X.A.B)" $
      relates_ SUP
      (TFunc (TTuple [TAny "a", TAny "a"])
            (TTuple [TAny "a", TAny "a"]))
      (TFunc (TTuple [TData ["X"],     TData ["X","A"]])
            (TTuple [TData ["X","A"], TData ["X","A","B"]]))
      `shouldBe` Right (TFunc (TTuple [TData ["X"],TData ["X","A"]]) (TTuple [TData ["X","A"],TData ["X","A","B"]]),[("a",TData ["X","A"])])
-}

  describe "supOf" $ do

    it "Int > BOT" $
      int `supOf` TBot       `shouldBe` (True,  TBot,       [])
    it "BOT > Int" $
      TBot       `supOf` int `shouldBe` (False, TBot,       [])
    it "a > Int" $
      TAny "a" `supOf` int `shouldBe` (True,  int, [("a",int,SUP)])
    it "a > b" $
      TAny "a" `supOf` TAny "b" `shouldBe` (True,TAny "b",[("a",TAny "b",SUP),("b",TAny "a",SUB)])
    it "b > b" $
      TAny "b" `supOf` TAny "b" `shouldBe` (True,TAny "b",[("b",TAny "b",SUP),("b",TAny "b",SUB)])

    it "Int > a" $
      supOf (TData ["Int"] [] TUnit) (TAny "a")
      `shouldBe` (True,TData ["Int"] [] TUnit,[("a",TData ["Int"] [] TUnit,SUB)])

    it "[I] > [a]" $
      supOf
        (TTuple [TData ["Int"] [] TUnit]) (TTuple [TAny "a"])
      `shouldBe` (True,TTuple [TData ["Int"] [] TUnit],[("a",TData ["Int"] [] TUnit,SUB)])

    it "P I > P a" $
      supOf
        (TData ["Pair"] [TData ["Int"] [] TUnit] (TTuple [TData ["Int"] [] TUnit]))
        (TData ["Pair"] [TAny "a"]              (TTuple [TAny "a"]))
      `shouldBe` (True,TData ["Pair"] [TData ["Int"] [] TUnit] (TTuple [TData ["Int"] [] TUnit]),[("a",TData ["Int"] [] TUnit,SUB)])

    it "P I I > P a a" $
      supOf
        (TData ["Pair"] [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit] (TTuple [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit]))
        (TData ["Pair"] [TAny "a",TAny "b"] (TTuple [TAny "a",TAny "b"]))
      `shouldBe` (True,TData ["Pair"] [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit] (TTuple [TData ["Int"] [] TUnit,TData ["Int"] [] TUnit]),[("a",TData ["Int"] [] TUnit,SUB),("b",TData ["Int"] [] TUnit,SUB)])

  describe "relates_" $ do

    it "b > b" $
      relates_ SUP (TAny "b") (TAny "b")
      `shouldBe` Right (TAny "b",[("b",TAny "b")])

    it "(a -> a) > (Int -> Int)" $
      relates_ SUP (TFunc (TAny "a") (TAny "a")) (TFunc (int) (int))
      `shouldBe` Right ((TFunc (int) (int)), [("a", int)])

    it "(a -> b) > (A -> B)" $
      relates_ SUP (TFunc (TAny "a") (TAny "b")) (TFunc (TData ["A"] [] TUnit) (TData ["B"] [] TUnit))
      `shouldBe` Right ((TFunc (TData ["A"] [] TUnit) (TData ["B"] [] TUnit)), [("a", TData ["A"] [] TUnit), ("b", TData ["B"] [] TUnit)])

    it "(a -> a) > (Int -> ())" $
      relates_ SUP (TFunc (TAny "a") (TAny "a")) (TFunc (int) TUnit)
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambiguous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates_ SUP (TTuple [(TAny "a"),(TAny "b")]) (TTuple [(int),TUnit])
      `shouldBe` Right (TTuple [int,TUnit],[("a",int),("b",TUnit)])

    it "(a,b,c) /> (Int,())" $
      relates_ SUP (TTuple [(TAny "a"),(TAny "b"),(TAny "c")]) (TTuple [(int),TUnit])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates_ SUP (TTuple [(TAny "a"),(TAny "b")]) (TTuple [(int),TUnit,(int)])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates_ SUP (TFunc (TAny "a") (TAny "a")) (TFunc (int) (int1))
      `shouldBe` Right (TFunc (int) (int1),[("a",int)])

    it "(Int -> Int.1) > (a -> a)" $
      relates_ SUP (TFunc (int) (int1)) (TFunc (TAny "a") (TAny "a"))
      `shouldBe` Left ["types do not match : expected '(Int -> Int.1)' : found '(a -> a)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates_ SUP (TFunc (int) (int)) (TFunc (int1) (int))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(Int.1 -> Int) > (a -> a)" $
      relates_ SUP (TFunc (int1) (int)) (TFunc (TAny "a") (TAny "a"))
      `shouldBe` Right (TFunc int1 int,[("a",int)])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates_ SUP (TFunc (boolt) (bool)) (TFunc (bool) (bool))
      `shouldBe` Right (TFunc (bool) (bool),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates_ SUP (TFunc (boolt) (bool)) (TFunc (bool) (boolt))
      `shouldBe` Right (TFunc (bool) (bool),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates_ SUP
      (TFunc (TTuple [TAny "a", TAny "a"])
             TUnit)
      (TFunc (TTuple [TData ["X"] [] TUnit, TData ["X","A"] [] TUnit])
             TUnit)
      `shouldBe` Right (TFunc (TTuple [TData ["X"] [] TUnit,TData ["X","A"] [] TUnit]) TUnit,[("a",TData ["X","A"] [] TUnit)])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates_ SUP
      (TFunc (TTuple [TAny "a", TAny "a"])
             TUnit)
      (TFunc (TTuple [TData ["Y"] [] TUnit, TData ["X","A"] [] TUnit])
             TUnit)
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambiguous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a)->(a,a)) SUP ((X,X.A)->(X.A,X.A.B)" $
      relates_ SUP
      (TFunc (TTuple [TAny "a", TAny "a"])
             (TTuple [TAny "a", TAny "a"]))
      (TFunc (TTuple [TData ["X"] [] TUnit,     TData ["X","A"] [] TUnit])
             (TTuple [TData ["X","A"] [] TUnit, TData ["X","A","B"] [] TUnit]))
      `shouldBe` Right (TFunc (TTuple [TData ["X"] [] TUnit,TData ["X","A"] [] TUnit]) (TTuple [TData ["X","A"] [] TUnit,TData ["X","A","B"] [] TUnit]),[("a",TData ["X","A"] [] TUnit)])

    it "((X,X.A)->(X.A,X.A.B) SUP ((a,a)->(a,a))" $
      relates_ SUP
      (TFunc (TTuple [TData ["X"] [] TUnit,     TData ["X","A"] [] TUnit])
             (TTuple [TData ["X","A"] [] TUnit, TData ["X","A","B"] [] TUnit]))
      (TFunc (TTuple [TAny "a", TAny "a"])
             (TTuple [TAny "a", TAny "a"]))
      `shouldBe` Left ["types do not match : expected '((X,X.A) -> (X.A,X.A.B))' : found '((a,a) -> (a,a))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates_ SUP
      (TFunc (TTuple [TAny "a", TAny "a"])
             (TTuple [TAny "a", TAny "a"]))
      (TFunc (TTuple [TData ["X"] [] TUnit, TData ["X","A"] [] TUnit])
             (TTuple [TData ["X"] [] TUnit, TData ["X","A","B"] [] TUnit]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A' should be supertype of 'X'"]

    it "(True,False)->() > (a,a)->()" $
      relates_ SUP
      (TFunc (TTuple [TData ["X","Bool","True"] [] TUnit, TData ["X","Bool","False"] [] TUnit]) TUnit)
      (TFunc (TTuple [TAny "a",                          TAny "a"])                           TUnit)
      `shouldBe` Right (TFunc (TTuple [TData ["X","Bool","True"] [] TUnit,TData ["X","Bool","False"] [] TUnit]) TUnit,[("a",TData ["X","Bool"] [] TUnit)])

    it "()->(True,False) SUP ()->(a,a)" $
      relates_ SUP
      (TFunc TUnit (TTuple [TData ["X","Bool","True"] [] TUnit, TData ["X","Bool","False"] [] TUnit]))
      (TFunc TUnit (TTuple [TAny "a",                 TAny "a"]))
      `shouldBe` Left ["types do not match : expected '(() -> (X.Bool.True,X.Bool.False))' : found '(() -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->(True,False) SUP (a,a)->(a,a)" $
      relates_ SUP
      (TFunc (TTuple [TData ["X","Bool","True"] [] TUnit, TData ["X","Bool","False"] [] TUnit])
             (TTuple [TData ["X","Bool","True"] [] TUnit, TData ["X","Bool","False"] [] TUnit]))
      (TFunc (TTuple [TAny "a", TAny "a"])
             (TTuple [TAny "a", TAny "a"]))
      `shouldBe` Left ["types do not match : expected '((X.Bool.True,X.Bool.False) -> (X.Bool.True,X.Bool.False))' : found '((a,a) -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False', 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->top SUP (a,a)->a" $
      relates_ SUP
      (TFunc (TTuple [boolt,     boolf])     TTop)
      (TFunc (TTuple [TAny "a", TAny "a"]) (TAny "a"))
      `shouldBe` Right (TFunc (TTuple [boolt,boolf]) bool,[("a",bool)])

    it "((1,2),(1,1))->? SUP (Int,Int)->Bool" $
      relates_ SUP
        (TFunc (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TAny "?"))
        (TFunc (TTuple [
                TTuple [int,int],
                TTuple [int,int]
              ])
              (bool))
      `shouldBe` Right (TFunc (TTuple [TTuple [int,int],TTuple [int,int]]) (bool),[("?",bool)])

    it "((1,2),(1,1))->? SUP (a,a)->Bool" $
      relates_ SUP
        (TFunc (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TAny "?"))
        (TFunc (TTuple [
                TAny "a",
                TAny "a"
              ])
              (bool))
      `shouldBe` Right (TFunc (TTuple [TTuple [int1,int2],TTuple [int1,int1]]) (bool),[("?",bool),("a",TTuple [int1,int])])

    it "((1,2),(1,1))->? SUB (a,a)->Bool" $
      relates_ SUP
        (TFunc (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TAny "?"))
        (TFunc (TTuple [
                TAny "a",
                TAny "a"
              ])
              (bool))
      `shouldBe` Right (TFunc (TTuple [TTuple [int1,int2],TTuple [int1,int1]]) (bool),[("?",bool),("a",TTuple [int1,int])])

    it "(a,a) > (370,10)" $
      relates_ SUP
        (TTuple [TAny "a",                   TAny "a"])
        (TTuple [TData ["Int","370"] [] TUnit,TData ["Int","10"] [] TUnit])
      `shouldBe` Right (TTuple [TData ["Int","370"] [] TUnit,TData ["Int","10"] [] TUnit],[("a",TData ["Int"] [] TUnit)])

    it "(a,a) > (X 370,X 10)" $
      relates_ SUP
        (TTuple [TAny "a",                                     TAny "a"])
        (TTuple [TData ["X"] [] $ TData ["Int","370"] [] TUnit, TData ["X"] [] $ TData ["Int","10"] [] TUnit])
      `shouldBe` Right (TTuple [TData ["X"] [] (TData ["Int","370"] [] TUnit),TData ["X"] [] (TData ["Int","10"] [] TUnit)],[("a",TData ["X"] [] (TData ["Int"] [] TUnit))])

    it "X of a" $
      relates_ SUP
        (TFunc TUnit       (TAny "?"))
        (TFunc (TAny "a") (TData ["X"] [TAny "a"] (TAny "a")))
        `shouldBe` Right (TFunc TUnit (TData ["X"] [TUnit] (TUnit)),[("?",TData ["X"] [TAny "a"] (TAny "a")),("a",TUnit)])

    it "X of a" $
      relates_ SUP
        (TTuple [TUnit,     TAny "?"])
        (TTuple [TAny "a", (TData ["X"] [TAny "a"] (TAny "a"))])
        `shouldBe` Right (TTuple [TUnit, TData ["X"] [TUnit] (TUnit)],[("?",TData ["X"] [TAny "a"] (TAny "a")),("a",TUnit)])

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TFunc TBot TTop `isSupOf_` TFunc TBot TTop
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TFunc TBot TTop `isSubOf_` TFunc TBot TTop
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TFunc TBot TTop `isSupOf_` TFunc TBot TBot
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TFunc TTop TTop `isSupOf_` TFunc TBot TBot
      `shouldBe` False

    it "top > Int" $
      TTop `isSupOf_` (int)
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TFunc TUnit TTop `isSupOf_` TFunc TUnit (int)
      `shouldBe` True

    it "Bool > Bool.True" $
      (bool `isSupOf_` boolt)
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",TData ["A"] [] TUnit), ("b",TData ["B"] [] TUnit)] (TData ["A"] [] TUnit)
      `shouldBe` (TData ["A"] [] TUnit)

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",TData ["A"] [] TUnit), ("b",TData ["B"] [] TUnit)] (TTuple [TAny "a", TAny "b"])
      `shouldBe` (TTuple [TData ["A"] [] TUnit, TData ["B"] [] TUnit])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",TData ["A"] [] TUnit), ("b",TData ["B"] [] TUnit)] (TFunc (TAny "a") (TData ["C"] [] TUnit))
      `shouldBe` (TFunc (TData ["A"] [] TUnit) (TData ["C"] [] TUnit))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (int) (int, int)
      `shouldBe` (int)

    it "Int : (a ~ Int) ~> Int" $
      inst' (int) (TAny "a", int)
      `shouldBe` (int)

    it "a : (a ~ Int) ~> Int" $
      inst' (TAny "a") (TAny "a", int)
      `shouldBe` (int)

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TAny "a") (TTuple [int,TAny "a"], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TAny "a") (TTuple [TAny "a",int], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TAny "a") (TTuple [TAny "a",TAny "a"], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TAny "a") (TTuple [TAny "a",TAny "a"], TTuple [int,bool])
      `shouldBe` TTop

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TAny "a") (TTuple [TAny "a",TAny "b"], TTuple [int,bool])
      `shouldBe` (int)

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TAny "b") (TTuple [TAny "a",TAny "b"], TTuple [int,bool])
      `shouldBe` (bool)

  describe "comPre" $ do

    it "[A.1,A.1]" $
      comPre [TData ["A","1"] [] TUnit, TData ["A","1"] [] TUnit]
      `shouldBe` Just (TData ["A","1"] [] TUnit)

    it "[A.1,A.2]" $
      comPre [TData ["A","1"] [] TUnit, TData ["A","2"] [] TUnit]
      `shouldBe` Just (TData ["A"] [] TUnit)

    it "[A.1,A.2,a]" $
      comPre [TData ["A","1"] [] TUnit, TData ["A","2"] [] TUnit, TAny "a"]
      `shouldBe` Just (TData ["A"] [] TUnit)

    it "[A.1,A.2,a,(A.1,a),(A.2,a)]" $
      comPre [TData ["A","1"] [] TUnit, TData ["A","2"] [] TUnit, TAny "a",
              TTuple [TData ["A","1"] [] TUnit, TAny "a"], TTuple [TData ["A","2"] [] TUnit, TAny "a"] ]
      `shouldBe` Just (TData ["A"] [] TUnit)

    it "[(A.1->A.2), (A.2->a)]" $
      comPre [TFunc (TData ["A","1"] [] TUnit) (TData ["A","2"] [] TUnit),
              TFunc (TData ["A","2"] [] TUnit) (TAny "a")]
      `shouldBe` Just (TFunc (TData ["A"] [] TUnit) (TData ["A","2"] [] TUnit))

    it "[a,(A.1,a),(A.2,a)]" $
      comPre [ TAny "a",
               TTuple [TData ["A","1"] [] TUnit, TAny "a"],
               TTuple [TData ["A","2"] [] TUnit, TAny "a"] ]
      `shouldBe` Just (TTuple [TData ["A"] [] TUnit,TAny "a"])

    it "[ [True,False] ]" $
      comPre [TTuple [boolt,boolf]]
      `shouldBe` Just (TTuple [boolt,boolf])

{-
    it "OK: [ [True,False], [True] ]" $ -- arity mismatch
      comPre [ TTuple [boolt,boolf],
               TTuple [boolt] ]
      `shouldBe` Just (TTuple [boolt,boolf])
-}

  describe "sort" $ do

    it "(Bool,Bool) <= Bool" $
      TTuple [TData ["Bool"] [] TUnit, TData ["Bool"] [] TUnit] <= TData ["Bool"] [] TUnit
      `shouldBe` False
    it "Bool <= (Bool,Bool)" $
      TData ["Bool"] [] TUnit <= TTuple [TData ["Bool"] [] TUnit, TData ["Bool"] [] TUnit]
      `shouldBe` True
    it "((Int,(Bool,Int)) <= (Bool,Int)" $
      TTuple [int, TTuple [bool,int]] <= TTuple [bool, int]
      `shouldBe` False
    it "(Bool,Int) <= ((Int,(Bool,Int))" $
      TTuple [bool, int] <= TTuple [int, TTuple [bool,int]]
      `shouldBe` True
    it "[Bool,Int] <= [Int,(Int,Int)]" $
      TTuple [bool, int] <= TTuple [int, TTuple [int,int]]
      `shouldBe` True
    it "list" $
      sort' [
        [TTuple [TData ["Bool"] [] TUnit,TData ["Bool"] [] TUnit],TTuple [TData ["Bool"] [] TUnit,TData ["Int"] [] TUnit]],
        [TData ["Int"] [] TUnit,TTuple [TData ["Bool"] [] TUnit,TData ["Int"] [] TUnit]]
       ]
      `shouldBe` [[TData ["Int"] [] TUnit,TTuple [TData ["Bool"] [] TUnit,TData ["Int"] [] TUnit]],[TTuple [TData ["Bool"] [] TUnit,TData ["Bool"] [] TUnit],TTuple [TData ["Bool"] [] TUnit,TData ["Int"] [] TUnit]]]
    it "list" $
      sort' [
        [TData ["Int"]  [] TUnit,TTuple [TData ["Int"]  [] TUnit,TData ["Int"] [] TUnit]],
        [TData ["Int"]  [] TUnit,TData ["Int"] [] TUnit]
       ]
      `shouldBe` [
        [TData ["Int"]  [] TUnit,TData ["Int"] [] TUnit],
        [TData ["Int"]  [] TUnit,TTuple [TData ["Int"]  [] TUnit,TData ["Int"] [] TUnit]]
       ]

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates_ SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TTop
