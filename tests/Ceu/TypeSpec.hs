module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

int  = TData False ["Int"]     [] (TUnit False)
int1 = TData False ["Int","1"] [] (TUnit False)
int2 = TData False ["Int","2"] [] (TUnit False)

bool  = TData False ["Bool"]         [] (TUnit False)
boolf = TData False ["Bool","False"] [] (TUnit False)
boolt = TData False ["Bool","True"]  [] (TUnit False)

spec :: Spec
spec = do

{-
  describe "TODO:" $ do

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X.A,X.A.B)" $
      relates_ SUP
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
            (TTuple False [TAny False "a", TAny False "a"]))
      (TFunc False (TTuple False [TData False ["X"],     TData False ["X","A"]])
            (TTuple False [TData False ["X","A"], TData False ["X","A","B"]]))
      `shouldBe` Right (TFunc False (TTuple False [TData False ["X"],TData False ["X","A"]]) (TTuple False [TData False ["X","A"],TData False ["X","A","B"]]),[("a",TData False ["X","A"])])
-}

  describe "supOf" $ do

    it "Int > BOT" $
      int `supOf` (TBot False)       `shouldBe` (True,  (TBot False),       [])
    it "BOT > Int" $
      (TBot False)       `supOf` int `shouldBe` (False, (TBot False),       [])
    it "a > Int" $
      TAny False "a" `supOf` int `shouldBe` (True,  int, [("a",int,SUP)])
    it "a > b" $
      TAny False "a" `supOf` TAny False "b" `shouldBe` (True,TAny False "b",[("a",TAny False "b",SUP),("b",TAny False "a",SUB)])
    it "b > b" $
      TAny False "b" `supOf` TAny False "b" `shouldBe` (True,TAny False "b",[("b",TAny False "b",SUP),("b",TAny False "b",SUB)])

    it "Int > a" $
      supOf (TData False ["Int"] [] (TUnit False)) (TAny False "a")
      `shouldBe` (True,TData False ["Int"] [] (TUnit False),[("a",TData False ["Int"] [] (TUnit False),SUB)])

    it "[I] > [a]" $
      supOf
        (TTuple False [TData False ["Int"] [] (TUnit False)]) (TTuple False [TAny False "a"])
      `shouldBe` (True,TTuple False [TData False ["Int"] [] (TUnit False)],[("a",TData False ["Int"] [] (TUnit False),SUB)])

    it "P I > P a" $
      supOf
        (TData False ["Pair"] [TData False ["Int"] [] (TUnit False)] (TTuple False [TData False ["Int"] [] (TUnit False)]))
        (TData False ["Pair"] [TAny False "a"]              (TTuple False [TAny False "a"]))
      `shouldBe` (True,TData False ["Pair"] [TData False ["Int"] [] (TUnit False)] (TTuple False [TData False ["Int"] [] (TUnit False)]),[("a",TData False ["Int"] [] (TUnit False),SUB)])

    it "P I I > P a a" $
      supOf
        (TData False ["Pair"] [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]))
        (TData False ["Pair"] [TAny False "a",TAny False "b"] (TTuple False [TAny False "a",TAny False "b"]))
      `shouldBe` (True,TData False ["Pair"] [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]),[("a",TData False ["Int"] [] (TUnit False),SUB),("b",TData False ["Int"] [] (TUnit False),SUB)])

  describe "relates_" $ do

    it "b > b" $
      relates_ SUP (TAny False "b") (TAny False "b")
      `shouldBe` Right (TAny False "b",[("b",TAny False "b")])

    it "(a -> a) > (Int -> Int)" $
      relates_ SUP (TFunc False (TAny False "a") (TAny False "a")) (TFunc False (int) (int))
      `shouldBe` Right ((TFunc False (int) (int)), [("a", int)])

    it "(a -> b) > (A -> B)" $
      relates_ SUP (TFunc False (TAny False "a") (TAny False "b")) (TFunc False (TData False ["A"] [] (TUnit False)) (TData False ["B"] [] (TUnit False)))
      `shouldBe` Right ((TFunc False (TData False ["A"] [] (TUnit False)) (TData False ["B"] [] (TUnit False))), [("a", TData False ["A"] [] (TUnit False)), ("b", TData False ["B"] [] (TUnit False))])

    it "(a -> a) > (Int -> ())" $
      relates_ SUP (TFunc False (TAny False "a") (TAny False "a")) (TFunc False (int) (TUnit False))
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambiguous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates_ SUP (TTuple False [(TAny False "a"),(TAny False "b")]) (TTuple False [(int),(TUnit False)])
      `shouldBe` Right (TTuple False [int,(TUnit False)],[("a",int),("b",(TUnit False))])

    it "(a,b,c) /> (Int,())" $
      relates_ SUP (TTuple False [(TAny False "a"),(TAny False "b"),(TAny False "c")]) (TTuple False [(int),(TUnit False)])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates_ SUP (TTuple False [(TAny False "a"),(TAny False "b")]) (TTuple False [(int),(TUnit False),(int)])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates_ SUP (TFunc False (TAny False "a") (TAny False "a")) (TFunc False (int) (int1))
      `shouldBe` Right (TFunc False (int) (int1),[("a",int)])

    it "(Int -> Int.1) > (a -> a)" $
      relates_ SUP (TFunc False (int) (int1)) (TFunc False (TAny False "a") (TAny False "a"))
      `shouldBe` Left ["types do not match : expected '(Int -> Int.1)' : found '(a -> a)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates_ SUP (TFunc False (int) (int)) (TFunc False (int1) (int))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(Int.1 -> Int) > (a -> a)" $
      relates_ SUP (TFunc False (int1) (int)) (TFunc False (TAny False "a") (TAny False "a"))
      `shouldBe` Right (TFunc False int1 int,[("a",int)])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates_ SUP (TFunc False (boolt) (bool)) (TFunc False (bool) (bool))
      `shouldBe` Right (TFunc False (bool) (bool),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates_ SUP (TFunc False (boolt) (bool)) (TFunc False (bool) (boolt))
      `shouldBe` Right (TFunc False (bool) (bool),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates_ SUP
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TUnit False))
      (TFunc False (TTuple False [TData False ["X"] [] (TUnit False), TData False ["X","A"] [] (TUnit False)])
             (TUnit False))
      `shouldBe` Right (TFunc False (TTuple False [TData False ["X"] [] (TUnit False),TData False ["X","A"] [] (TUnit False)]) (TUnit False),[("a",TData False ["X","A"] [] (TUnit False))])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates_ SUP
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TUnit False))
      (TFunc False (TTuple False [TData False ["Y"] [] (TUnit False), TData False ["X","A"] [] (TUnit False)])
             (TUnit False))
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambiguous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a)->(a,a)) SUP ((X,X.A)->(X.A,X.A.B)" $
      relates_ SUP
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TTuple False [TAny False "a", TAny False "a"]))
      (TFunc False (TTuple False [TData False ["X"] [] (TUnit False),     TData False ["X","A"] [] (TUnit False)])
             (TTuple False [TData False ["X","A"] [] (TUnit False), TData False ["X","A","B"] [] (TUnit False)]))
      `shouldBe` Right (TFunc False (TTuple False [TData False ["X"] [] (TUnit False),TData False ["X","A"] [] (TUnit False)]) (TTuple False [TData False ["X","A"] [] (TUnit False),TData False ["X","A","B"] [] (TUnit False)]),[("a",TData False ["X","A"] [] (TUnit False))])

    it "((X,X.A)->(X.A,X.A.B) SUP ((a,a)->(a,a))" $
      relates_ SUP
      (TFunc False (TTuple False [TData False ["X"] [] (TUnit False),     TData False ["X","A"] [] (TUnit False)])
             (TTuple False [TData False ["X","A"] [] (TUnit False), TData False ["X","A","B"] [] (TUnit False)]))
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TTuple False [TAny False "a", TAny False "a"]))
      `shouldBe` Left ["types do not match : expected '((X,X.A) -> (X.A,X.A.B))' : found '((a,a) -> (a,a))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates_ SUP
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TTuple False [TAny False "a", TAny False "a"]))
      (TFunc False (TTuple False [TData False ["X"] [] (TUnit False), TData False ["X","A"] [] (TUnit False)])
             (TTuple False [TData False ["X"] [] (TUnit False), TData False ["X","A","B"] [] (TUnit False)]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A' should be supertype of 'X'"]

    it "(True,False)->() > (a,a)->()" $
      relates_ SUP
      (TFunc False (TTuple False [TData False ["X","Bool","True"] [] (TUnit False), TData False ["X","Bool","False"] [] (TUnit False)]) (TUnit False))
      (TFunc False (TTuple False [TAny False "a",                          TAny False "a"])                           (TUnit False))
      `shouldBe` Right (TFunc False (TTuple False [TData False ["X","Bool","True"] [] (TUnit False),TData False ["X","Bool","False"] [] (TUnit False)]) (TUnit False),[("a",TData False ["X","Bool"] [] (TUnit False))])

    it "()->(True,False) SUP ()->(a,a)" $
      relates_ SUP
      (TFunc False (TUnit False) (TTuple False [TData False ["X","Bool","True"] [] (TUnit False), TData False ["X","Bool","False"] [] (TUnit False)]))
      (TFunc False (TUnit False) (TTuple False [TAny False "a",                 TAny False "a"]))
      `shouldBe` Left ["types do not match : expected '(() -> (X.Bool.True,X.Bool.False))' : found '(() -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->(True,False) SUP (a,a)->(a,a)" $
      relates_ SUP
      (TFunc False (TTuple False [TData False ["X","Bool","True"] [] (TUnit False), TData False ["X","Bool","False"] [] (TUnit False)])
             (TTuple False [TData False ["X","Bool","True"] [] (TUnit False), TData False ["X","Bool","False"] [] (TUnit False)]))
      (TFunc False (TTuple False [TAny False "a", TAny False "a"])
             (TTuple False [TAny False "a", TAny False "a"]))
      `shouldBe` Left ["types do not match : expected '((X.Bool.True,X.Bool.False) -> (X.Bool.True,X.Bool.False))' : found '((a,a) -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False', 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->top SUP (a,a)->a" $
      relates_ SUP
      (TFunc False (TTuple False [boolt,     boolf])     (TTop False))
      (TFunc False (TTuple False [TAny False "a", TAny False "a"]) (TAny False "a"))
      `shouldBe` Right (TFunc False (TTuple False [boolt,boolf]) bool,[("a",bool)])

    it "((1,2),(1,1))->? SUP (Int,Int)->Bool" $
      relates_ SUP
        (TFunc False (TTuple False [
                TTuple False [int1,int2],
                TTuple False [int1,int1]
              ])
              (TAny False "?"))
        (TFunc False (TTuple False [
                TTuple False [int,int],
                TTuple False [int,int]
              ])
              (bool))
      `shouldBe` Right (TFunc False (TTuple False [TTuple False [int,int],TTuple False [int,int]]) (bool),[("?",bool)])

    it "((1,2),(1,1))->? SUP (a,a)->Bool" $
      relates_ SUP
        (TFunc False (TTuple False [
                TTuple False [int1,int2],
                TTuple False [int1,int1]
              ])
              (TAny False "?"))
        (TFunc False (TTuple False [
                TAny False "a",
                TAny False "a"
              ])
              (bool))
      `shouldBe` Right (TFunc False (TTuple False [TTuple False [int1,int2],TTuple False [int1,int1]]) (bool),[("?",bool),("a",TTuple False [int1,int])])

    it "((1,2),(1,1))->? SUB (a,a)->Bool" $
      relates_ SUP
        (TFunc False (TTuple False [
                TTuple False [int1,int2],
                TTuple False [int1,int1]
              ])
              (TAny False "?"))
        (TFunc False (TTuple False [
                TAny False "a",
                TAny False "a"
              ])
              (bool))
      `shouldBe` Right (TFunc False (TTuple False [TTuple False [int1,int2],TTuple False [int1,int1]]) (bool),[("?",bool),("a",TTuple False [int1,int])])

    it "(a,a) > (370,10)" $
      relates_ SUP
        (TTuple False [TAny False "a",                   TAny False "a"])
        (TTuple False [TData False ["Int","370"] [] (TUnit False),TData False ["Int","10"] [] (TUnit False)])
      `shouldBe` Right (TTuple False [TData False ["Int","370"] [] (TUnit False),TData False ["Int","10"] [] (TUnit False)],[("a",TData False ["Int"] [] (TUnit False))])

    it "(a,a) > (X 370,X 10)" $
      relates_ SUP
        (TTuple False [TAny False "a",                                     TAny False "a"])
        (TTuple False [TData False ["X"] [] $ TData False ["Int","370"] [] (TUnit False), TData False ["X"] [] $ TData False ["Int","10"] [] (TUnit False)])
      `shouldBe` Right (TTuple False [TData False ["X"] [] (TData False ["Int","370"] [] (TUnit False)),TData False ["X"] [] (TData False ["Int","10"] [] (TUnit False))],[("a",TData False ["X"] [] (TData False ["Int"] [] (TUnit False)))])

    it "X of a" $
      relates_ SUP
        (TFunc False (TUnit False)       (TAny False "?"))
        (TFunc False (TAny False "a") (TData False ["X"] [TAny False "a"] (TAny False "a")))
        `shouldBe` Right (TFunc False (TUnit False) (TData False ["X"] [(TUnit False)] ((TUnit False))),[("?",TData False ["X"] [TAny False "a"] (TAny False "a")),("a",(TUnit False))])

    it "X of a" $
      relates_ SUP
        (TTuple False [(TUnit False),     TAny False "?"])
        (TTuple False [TAny False "a", (TData False ["X"] [TAny False "a"] (TAny False "a"))])
        `shouldBe` Right (TTuple False [(TUnit False), TData False ["X"] [(TUnit False)] ((TUnit False))],[("?",TData False ["X"] [TAny False "a"] (TAny False "a")),("a",(TUnit False))])

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TFunc False (TBot False) (TTop False) `isSupOf_` TFunc False (TBot False) (TTop False)
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TFunc False (TBot False) (TTop False) `isSubOf_` TFunc False (TBot False) (TTop False)
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TFunc False (TBot False) (TTop False) `isSupOf_` TFunc False (TBot False) (TBot False)
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TFunc False (TTop False) (TTop False) `isSupOf_` TFunc False (TBot False) (TBot False)
      `shouldBe` False

    it "top > Int" $
      (TTop False) `isSupOf_` (int)
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TFunc False (TUnit False) (TTop False) `isSupOf_` TFunc False (TUnit False) (int)
      `shouldBe` True

    it "Bool > Bool.True" $
      (bool `isSupOf_` boolt)
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",TData False ["A"] [] (TUnit False)), ("b",TData False ["B"] [] (TUnit False))] (TData False ["A"] [] (TUnit False))
      `shouldBe` (TData False ["A"] [] (TUnit False))

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",TData False ["A"] [] (TUnit False)), ("b",TData False ["B"] [] (TUnit False))] (TTuple False [TAny False "a", TAny False "b"])
      `shouldBe` (TTuple False [TData False ["A"] [] (TUnit False), TData False ["B"] [] (TUnit False)])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",TData False ["A"] [] (TUnit False)), ("b",TData False ["B"] [] (TUnit False))] (TFunc False (TAny False "a") (TData False ["C"] [] (TUnit False)))
      `shouldBe` (TFunc False (TData False ["A"] [] (TUnit False)) (TData False ["C"] [] (TUnit False)))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (int) (int, int)
      `shouldBe` (int)

    it "Int : (a ~ Int) ~> Int" $
      inst' (int) (TAny False "a", int)
      `shouldBe` (int)

    it "a : (a ~ Int) ~> Int" $
      inst' (TAny False "a") (TAny False "a", int)
      `shouldBe` (int)

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TAny False "a") (TTuple False [int,TAny False "a"], TTuple False [int,int])
      `shouldBe` (int)

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TAny False "a") (TTuple False [TAny False "a",int], TTuple False [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TAny False "a") (TTuple False [TAny False "a",TAny False "a"], TTuple False [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TAny False "a") (TTuple False [TAny False "a",TAny False "a"], TTuple False [int,bool])
      `shouldBe` (TTop False)

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TAny False "a") (TTuple False [TAny False "a",TAny False "b"], TTuple False [int,bool])
      `shouldBe` (int)

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TAny False "b") (TTuple False [TAny False "a",TAny False "b"], TTuple False [int,bool])
      `shouldBe` (bool)

  describe "comPre" $ do

    it "[A.1,A.1]" $
      comPre [TData False ["A","1"] [] (TUnit False), TData False ["A","1"] [] (TUnit False)]
      `shouldBe` Just (TData False ["A","1"] [] (TUnit False))

    it "[A.1,A.2]" $
      comPre [TData False ["A","1"] [] (TUnit False), TData False ["A","2"] [] (TUnit False)]
      `shouldBe` Just (TData False ["A"] [] (TUnit False))

    it "[A.1,A.2,a]" $
      comPre [TData False ["A","1"] [] (TUnit False), TData False ["A","2"] [] (TUnit False), TAny False "a"]
      `shouldBe` Just (TData False ["A"] [] (TUnit False))

    it "[A.1,A.2,a,(A.1,a),(A.2,a)]" $
      comPre [TData False ["A","1"] [] (TUnit False), TData False ["A","2"] [] (TUnit False), TAny False "a",
              TTuple False [TData False ["A","1"] [] (TUnit False), TAny False "a"], TTuple False [TData False ["A","2"] [] (TUnit False), TAny False "a"] ]
      `shouldBe` Just (TData False ["A"] [] (TUnit False))

    it "[(A.1->A.2), (A.2->a)]" $
      comPre [TFunc False (TData False ["A","1"] [] (TUnit False)) (TData False ["A","2"] [] (TUnit False)),
              TFunc False (TData False ["A","2"] [] (TUnit False)) (TAny False "a")]
      `shouldBe` Just (TFunc False (TData False ["A"] [] (TUnit False)) (TData False ["A","2"] [] (TUnit False)))

    it "[a,(A.1,a),(A.2,a)]" $
      comPre [ TAny False "a",
               TTuple False [TData False ["A","1"] [] (TUnit False), TAny False "a"],
               TTuple False [TData False ["A","2"] [] (TUnit False), TAny False "a"] ]
      `shouldBe` Just (TTuple False [TData False ["A"] [] (TUnit False),TAny False "a"])

    it "[ [True,False] ]" $
      comPre [TTuple False [boolt,boolf]]
      `shouldBe` Just (TTuple False [boolt,boolf])

{-
    it "OK: [ [True,False], [True] ]" $ -- arity mismatch
      comPre [ TTuple False [boolt,boolf],
               TTuple False [boolt] ]
      `shouldBe` Just (TTuple False [boolt,boolf])
-}

  describe "sort" $ do

    it "(Bool,Bool) <= Bool" $
      TTuple False [TData False ["Bool"] [] (TUnit False), TData False ["Bool"] [] (TUnit False)] <= TData False ["Bool"] [] (TUnit False)
      `shouldBe` False
    it "Bool <= (Bool,Bool)" $
      TData False ["Bool"] [] (TUnit False) <= TTuple False [TData False ["Bool"] [] (TUnit False), TData False ["Bool"] [] (TUnit False)]
      `shouldBe` True
    it "((Int,(Bool,Int)) <= (Bool,Int)" $
      TTuple False [int, TTuple False [bool,int]] <= TTuple False [bool, int]
      `shouldBe` False
    it "(Bool,Int) <= ((Int,(Bool,Int))" $
      TTuple False [bool, int] <= TTuple False [int, TTuple False [bool,int]]
      `shouldBe` True
    it "[Bool,Int] <= [Int,(Int,Int)]" $
      TTuple False [bool, int] <= TTuple False [int, TTuple False [int,int]]
      `shouldBe` True
    it "list" $
      sort' [
        [TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Bool"] [] (TUnit False)],TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]],
        [TData False ["Int"] [] (TUnit False),TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]]
       ]
      `shouldBe` [[TData False ["Int"] [] (TUnit False),TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]],[TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Bool"] [] (TUnit False)],TTuple False [TData False ["Bool"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]]]
    it "list" $
      sort' [
        [TData False ["Int"]  [] (TUnit False),TTuple False [TData False ["Int"]  [] (TUnit False),TData False ["Int"] [] (TUnit False)]],
        [TData False ["Int"]  [] (TUnit False),TData False ["Int"] [] (TUnit False)]
       ]
      `shouldBe` [
        [TData False ["Int"]  [] (TUnit False),TData False ["Int"] [] (TUnit False)],
        [TData False ["Int"]  [] (TUnit False),TTuple False [TData False ["Int"]  [] (TUnit False),TData False ["Int"] [] (TUnit False)]]
       ]

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates_ SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> (TTop False)
