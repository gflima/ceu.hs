module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

int  = TData False ["Int"]     []
int1 = TData False ["Int","1"] []
int2 = TData False ["Int","2"] []

bool  = TData False ["Bool"]         []
boolf = TData False ["Bool","False"] []
boolt = TData False ["Bool","True"]  []

spec :: Spec
spec = do

{-
  describe "TODO:" $ do

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X.A,X.A.B)" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
            (TTuple [TVar False "a", TVar False "a"]))
      (TFunc FuncGlobal (TTuple [TData False ["X"],     TData False ["X","A"]])
            (TTuple [TData False ["X","A"], TData False ["X","A","B"]]))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TData False ["X"],TData False ["X","A"]]) (TTuple [TData False ["X","A"],TData False ["X","A","B"]]),[("a",TData False ["X","A"])])
-}

  describe "supOf" $ do

    it "Int > BOT" $
      int `supOf` TBot `shouldBe` (True, TBot, [])
    it "BOT > Int" $
      TBot `supOf` int `shouldBe` (False, TBot, [])
    it "a > Int" $
      TVar False "a" `supOf` int `shouldBe` (True,  int, [("a",int,SUP)])
    it "a > b" $
      TVar False "a" `supOf` TVar False "b" `shouldBe` (True,TVar False "b",[("a",TVar False "b",SUP),("b",TVar False "a",SUB)])
    it "b > b" $
      TVar False "b" `supOf` TVar False "b" `shouldBe` (True,TVar False "b",[("b",TVar False "b",SUP),("b",TVar False "b",SUB)])

    it "Int > a" $
      supOf (TData False ["Int"] []) (TVar False "a")
      `shouldBe` (True,TData False ["Int"] [],[("a",TData False ["Int"] [],SUB)])

    it "[I] > [a]" $
      supOf
        (TTuple [TData False ["Int"] []]) (TTuple [TVar False "a"])
      `shouldBe` (True,TTuple [TData False ["Int"] []],[("a",TData False ["Int"] [],SUB)])

    it "P I > P a" $
      supOf
        (TData False ["Pair"] [TData False ["Int"] []])
        (TData False ["Pair"] [TVar False "a"]     )
      `shouldBe` (True,TData False ["Pair"] [TData False ["Int"] []],[("a",TData False ["Int"] [],SUB)])

    it "P I I > P a a" $
      supOf
        (TData False ["Pair"] [TData False ["Int"] [],TData False ["Int"] []])
        (TData False ["Pair"] [TVar False "a",TVar False "b"] )
      `shouldBe` (True,TData False ["Pair"] [TData False ["Int"] [],TData False ["Int"] []],[("a",TData False ["Int"] [],SUB),("b",TData False ["Int"] [],SUB)])

  describe "relates" $ do

    it "b > b" $
      relates SUP (TVar False "b") (TVar False "b")
      `shouldBe` Right (TVar False "b",[("b",TVar False "b")])

    it "(a -> a) > (Int -> Int)" $
      relates SUP (TFunc FuncGlobal (TVar False "a") (TVar False "a")) (TFunc FuncGlobal (int) (int))
      `shouldBe` Right ((TFunc FuncGlobal (int) (int)), [("a", int)])

    it "(a -> b) > (A -> B)" $
      relates SUP (TFunc FuncGlobal (TVar False "a") (TVar False "b")) (TFunc FuncGlobal (TData False ["A"] []) (TData False ["B"] []))
      `shouldBe` Right ((TFunc FuncGlobal (TData False ["A"] []) (TData False ["B"] [])), [("a", TData False ["A"] []), ("b", TData False ["B"] [])])

    it "(a -> a) > (Int -> ())" $
      relates SUP (TFunc FuncGlobal (TVar False "a") (TVar False "a")) (TFunc FuncGlobal (int) TUnit)
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambiguous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      relates SUP (TTuple [(TVar False "a"),(TVar False "b")]) (TTuple [(int),TUnit])
      `shouldBe` Right (TTuple [int,TUnit],[("a",int),("b",TUnit)])

    it "(a,b,c) /> (Int,())" $
      relates SUP (TTuple [(TVar False "a"),(TVar False "b"),(TVar False "c")]) (TTuple [(int),TUnit])
      `shouldBe` Left ["types do not match : expected '(a,b,c)' : found '(Int,())'"]

    it "(a,b) /> (Int,(),Int)" $
      relates SUP (TTuple [(TVar False "a"),(TVar False "b")]) (TTuple [(int),TUnit,(int)])
      `shouldBe` Left ["types do not match : expected '(a,b)' : found '(Int,(),Int)'"]

    it "(a -> a) > (Int -> Int.1)" $
      relates SUP (TFunc FuncGlobal (TVar False "a") (TVar False "a")) (TFunc FuncGlobal (int) (int1))
      `shouldBe` Right (TFunc FuncGlobal (int) (int1),[("a",int)])

    it "(Int -> Int.1) > (a -> a)" $
      relates SUP (TFunc FuncGlobal (int) (int1)) (TFunc FuncGlobal (TVar False "a") (TVar False "a"))
      `shouldBe` Left ["types do not match : expected '(Int -> Int.1)' : found '(a -> a)'","type variance does not match : 'Int.1' should be supertype of 'Int'"]

    it "(Int -> Int) /> (Int.1 -> Int)" $
      relates SUP (TFunc FuncGlobal (int) (int)) (TFunc FuncGlobal (int1) (int))
      `shouldBe` Left ["types do not match : expected '(Int -> Int)' : found '(Int.1 -> Int)'"]

    it "(Int.1 -> Int) > (a -> a)" $
      relates SUP (TFunc FuncGlobal (int1) (int)) (TFunc FuncGlobal (TVar False "a") (TVar False "a"))
      `shouldBe` Right (TFunc FuncGlobal int1 int,[("a",int)])

    it "(True -> Bool) > (Bool -> Bool)" $
      relates SUP (TFunc FuncGlobal (boolt) (bool)) (TFunc FuncGlobal (bool) (bool))
      `shouldBe` Right (TFunc FuncGlobal (bool) (bool),[])

    it "(True -> Bool) > (Bool -> True)" $
      relates SUP (TFunc FuncGlobal (boolt) (bool)) (TFunc FuncGlobal (bool) (boolt))
      `shouldBe` Right (TFunc FuncGlobal (bool) (bool),[])

    it "((a,a) -> ()) > ((X,X.A) -> ()" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             TUnit)
      (TFunc FuncGlobal (TTuple [TData False ["X"] [], TData False ["X","A"] []])
             TUnit)
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TData False ["X"] [],TData False ["X","A"] []]) TUnit,[("a",TData False ["X","A"] [])])

    it "((a,a) -> ()) > ((Y,X.A) -> ()" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             TUnit)
      (TFunc FuncGlobal (TTuple [TData False ["Y"] [], TData False ["X","A"] []])
             TUnit)
      `shouldBe` Left ["types do not match : expected '((a,a) -> ())' : found '((Y,X.A) -> ())'","ambiguous instances for 'a' : 'Y', 'X.A'"]

    it "((a,a)->(a,a)) SUP ((X,X.A)->(X.A,X.A.B)" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             (TTuple [TVar False "a", TVar False "a"]))
      (TFunc FuncGlobal (TTuple [TData False ["X"] [],     TData False ["X","A"] []])
             (TTuple [TData False ["X","A"] [], TData False ["X","A","B"] []]))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TData False ["X"] [],TData False ["X","A"] []]) (TTuple [TData False ["X","A"] [],TData False ["X","A","B"] []]),[("a",TData False ["X","A"] [])])

    it "((X,X.A)->(X.A,X.A.B) SUP ((a,a)->(a,a))" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TData False ["X"] [],     TData False ["X","A"] []])
             (TTuple [TData False ["X","A"] [], TData False ["X","A","B"] []]))
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             (TTuple [TVar False "a", TVar False "a"]))
      `shouldBe` Left ["types do not match : expected '((X,X.A) -> (X.A,X.A.B))' : found '((a,a) -> (a,a))'","type variance does not match : 'X.A.B' should be supertype of 'X'"]

    it "((a,a) -> (a,a)) > ((X,X.A) -> (X,X.A.B)" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             (TTuple [TVar False "a", TVar False "a"]))
      (TFunc FuncGlobal (TTuple [TData False ["X"] [], TData False ["X","A"] []])
             (TTuple [TData False ["X"] [], TData False ["X","A","B"] []]))
      `shouldBe` Left ["types do not match : expected '((a,a) -> (a,a))' : found '((X,X.A) -> (X,X.A.B))'","type variance does not match : 'X.A' should be supertype of 'X'"]

    it "(True,False)->() > (a,a)->()" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TData False ["X","Bool","True"] [], TData False ["X","Bool","False"] []]) TUnit)
      (TFunc FuncGlobal (TTuple [TVar False "a",                          TVar False "a"])                           TUnit)
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TData False ["X","Bool","True"] [],TData False ["X","Bool","False"] []]) TUnit,[("a",TData False ["X","Bool"] [])])

    it "()->(True,False) SUP ()->(a,a)" $
      relates SUP
      (TFunc FuncGlobal TUnit (TTuple [TData False ["X","Bool","True"] [], TData False ["X","Bool","False"] []]))
      (TFunc FuncGlobal TUnit (TTuple [TVar False "a",                 TVar False "a"]))
      `shouldBe` Left ["types do not match : expected '(() -> (X.Bool.True,X.Bool.False))' : found '(() -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->(True,False) SUP (a,a)->(a,a)" $
      relates SUP
      (TFunc FuncGlobal (TTuple [TData False ["X","Bool","True"] [], TData False ["X","Bool","False"] []])
             (TTuple [TData False ["X","Bool","True"] [], TData False ["X","Bool","False"] []]))
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"])
             (TTuple [TVar False "a", TVar False "a"]))
      `shouldBe` Left ["types do not match : expected '((X.Bool.True,X.Bool.False) -> (X.Bool.True,X.Bool.False))' : found '((a,a) -> (a,a))'","ambiguous instances for 'a' : 'X.Bool.True', 'X.Bool.False', 'X.Bool.True', 'X.Bool.False'"]

    it "(True,False)->top SUP (a,a)->a" $
      relates SUP
      (TFunc FuncGlobal (TTuple [boolt,     boolf])     TTop)
      (TFunc FuncGlobal (TTuple [TVar False "a", TVar False "a"]) (TVar False "a"))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [boolt,boolf]) bool,[("a",bool)])

    it "((1,2),(1,1))->? SUP (Int,Int)->Bool" $
      relates SUP
        (TFunc FuncGlobal (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TVar False "?"))
        (TFunc FuncGlobal (TTuple [
                TTuple [int,int],
                TTuple [int,int]
              ])
              (bool))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TTuple [int,int],TTuple [int,int]]) (bool),[("?",bool)])

    it "ref Int vs Int" $
      relates SUP
        (TData False ["Int"] [])
        (TData True  ["Int"] [])
      `shouldBe` Left ["types do not match : expected 'Int' : found 'ref Int'"]

    it "ref Int vs Int" $
      relates SUP
        (TFunc FuncUnknown (TData False ["Int"] []) TTop)
        (TFunc FuncUnknown (TData True ["Int"] []) TUnit)
      `shouldBe` Left ["types do not match : expected '(Int -> top)' : found '(ref Int -> ())'"]

    it "ref Int vs Int" $
      relates SUP
        (TFunc FuncUnknown (TData False ["Int"] []) TAny)
        (TFunc FuncUnknown (TData True ["Int"] []) TUnit)
      `shouldBe` Left ["types do not match : expected '(Int -> ?)' : found '(ref Int -> ())'"]

    it "((1,2),(1,1))->? SUP (a,a)->Bool" $
      relates SUP
        (TFunc FuncGlobal (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TVar False "?"))
        (TFunc FuncGlobal (TTuple [
                TVar False "a",
                TVar False "a"
              ])
              (bool))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TTuple [int1,int2],TTuple [int1,int1]]) (bool),[("?",bool),("a",TTuple [int1,int])])

    it "((1,2),(1,1))->? SUB (a,a)->Bool" $
      relates SUP
        (TFunc FuncGlobal (TTuple [
                TTuple [int1,int2],
                TTuple [int1,int1]
              ])
              (TVar False "?"))
        (TFunc FuncGlobal (TTuple [
                TVar False "a",
                TVar False "a"
              ])
              (bool))
      `shouldBe` Right (TFunc FuncGlobal (TTuple [TTuple [int1,int2],TTuple [int1,int1]]) (bool),[("?",bool),("a",TTuple [int1,int])])

    it "(a,a) > (370,10)" $
      relates SUP
        (TTuple [TVar False "a",                   TVar False "a"])
        (TTuple [TData False ["Int","370"] [],TData False ["Int","10"] []])
      `shouldBe` Right (TTuple [TData False ["Int","370"] [],TData False ["Int","10"] []],[("a",TData False ["Int"] [])])

    it "(a,a) > (X 370,X 10)" $
      relates SUP
        (TTuple [TVar False "a",       TVar False "a"])
        (TTuple [TData False ["X"] [], TData False ["X"] []])
      `shouldBe` Right (TTuple [TData False ["X"] [],TData False ["X"] []],[("a",TData False ["X"] [])])

    it "X of a" $
      relates SUP
        (TFunc FuncGlobal TUnit       (TVar False "?"))
        (TFunc FuncGlobal (TVar False "a") (TData False ["X"] [TVar False "a"]))
        `shouldBe` Right (TFunc FuncGlobal TUnit (TData False ["X"] [TUnit]),[("?",TData False ["X"] [TVar False "a"]),("a",TUnit)])

    it "X of a" $
      relates SUP
        (TTuple [TUnit,     TVar False "?"])
        (TTuple [TVar False "a", (TData False ["X"] [TVar False "a"])])
        `shouldBe` Right (TTuple [TUnit, TData False ["X"] [TUnit]],[("?",TData False ["X"] [TVar False "a"]),("a",TUnit)])

  describe "isSupOf / isSubOf" $ do

    it "(bot -> top) > (bot -> top)" $
      TFunc FuncGlobal TBot TTop `isSupOf` TFunc FuncGlobal TBot TTop
      `shouldBe` True
    it "(bot -> top) < (bot -> top)" $
      TFunc FuncGlobal TBot TTop `isSubOf` TFunc FuncGlobal TBot TTop
      `shouldBe` True

    it "(bot -> top) > (bot -> bot)" $
      TFunc FuncGlobal TBot TTop `isSupOf` TFunc FuncGlobal TBot TBot
      `shouldBe` True
    it "(top -> top) > (bot -> bot)" $
      TFunc FuncGlobal TTop TTop `isSupOf` TFunc FuncGlobal TBot TBot
      `shouldBe` False

    it "top > Int" $
      TTop `isSupOf` (int)
      `shouldBe` True
    it "(() -> top) > (() -> Int)" $
      TFunc FuncGlobal TUnit TTop `isSupOf` TFunc FuncGlobal TUnit (int)
      `shouldBe` True

    it "Bool > Bool.True" $
      (bool `isSupOf` boolt)
      `shouldBe` True

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",TData False ["A"] []), ("b",TData False ["B"] [])] (TData False ["A"] [])
      `shouldBe` (TData False ["A"] [])

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",TData False ["A"] []), ("b",TData False ["B"] [])] (TTuple [TVar False "a", TVar False "b"])
      `shouldBe` (TTuple [TData False ["A"] [], TData False ["B"] []])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",TData False ["A"] []), ("b",TData False ["B"] [])] (TFunc FuncGlobal (TVar False "a") (TData False ["C"] []))
      `shouldBe` (TFunc FuncGlobal (TData False ["A"] []) (TData False ["C"] []))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (int) (int, int)
      `shouldBe` (int)

    it "Int : (a ~ Int) ~> Int" $
      inst' (int) (TVar False "a", int)
      `shouldBe` (int)

    it "a : (a ~ Int) ~> Int" $
      inst' (TVar False "a") (TVar False "a", int)
      `shouldBe` (int)

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TVar False "a") (TTuple [int,TVar False "a"], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TVar False "a") (TTuple [TVar False "a",int], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TVar False "a") (TTuple [TVar False "a",TVar False "a"], TTuple [int,int])
      `shouldBe` (int)

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TVar False "a") (TTuple [TVar False "a",TVar False "a"], TTuple [int,bool])
      `shouldBe` TTop

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TVar False "a") (TTuple [TVar False "a",TVar False "b"], TTuple [int,bool])
      `shouldBe` (int)

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TVar False "b") (TTuple [TVar False "a",TVar False "b"], TTuple [int,bool])
      `shouldBe` (bool)

  describe "comPre" $ do

    it "[A.1,A.1]" $
      comPre [TData False ["A","1"] [], TData False ["A","1"] []]
      `shouldBe` Just (TData False ["A","1"] [])

    it "[A.1,A.2]" $
      comPre [TData False ["A","1"] [], TData False ["A","2"] []]
      `shouldBe` Just (TData False ["A"] [])

    it "[A.1,A.2,a]" $
      comPre [TData False ["A","1"] [], TData False ["A","2"] [], TVar False "a"]
      `shouldBe` Just (TData False ["A"] [])

    it "[A.1,A.2,a,(A.1,a),(A.2,a)]" $
      comPre [TData False ["A","1"] [], TData False ["A","2"] [], TVar False "a",
              TTuple [TData False ["A","1"] [], TVar False "a"], TTuple [TData False ["A","2"] [], TVar False "a"] ]
      `shouldBe` Just (TData False ["A"] [])

    it "[(A.1->A.2), (A.2->a)]" $
      comPre [TFunc FuncGlobal (TData False ["A","1"] []) (TData False ["A","2"] []),
              TFunc FuncGlobal (TData False ["A","2"] []) (TVar False "a")]
      `shouldBe` Just (TFunc FuncGlobal (TData False ["A"] []) (TData False ["A","2"] []))

    it "[a,(A.1,a),(A.2,a)]" $
      comPre [ TVar False "a",
               TTuple [TData False ["A","1"] [], TVar False "a"],
               TTuple [TData False ["A","2"] [], TVar False "a"] ]
      `shouldBe` Just (TTuple [TData False ["A"] [],TVar False "a"])

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
      TTuple [TData False ["Bool"] [], TData False ["Bool"] []] <= TData False ["Bool"] []
      `shouldBe` False
    it "Bool <= (Bool,Bool)" $
      TData False ["Bool"] [] <= TTuple [TData False ["Bool"] [], TData False ["Bool"] []]
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
        [TTuple [TData False ["Bool"] [],TData False ["Bool"] []],TTuple [TData False ["Bool"] [],TData False ["Int"] []]],
        [TData False ["Int"] [],TTuple [TData False ["Bool"] [],TData False ["Int"] []]]
       ]
      `shouldBe` [[TData False ["Int"] [],TTuple [TData False ["Bool"] [],TData False ["Int"] []]],[TTuple [TData False ["Bool"] [],TData False ["Bool"] []],TTuple [TData False ["Bool"] [],TData False ["Int"] []]]]
    it "list" $
      sort' [
        [TData False ["Int"]  [],TTuple [TData False ["Int"]  [],TData False ["Int"] []]],
        [TData False ["Int"]  [],TData False ["Int"] []]
       ]
      `shouldBe` [
        [TData False ["Int"]  [],TData False ["Int"] []],
        [TData False ["Int"]  [],TTuple [TData False ["Int"]  [],TData False ["Int"] []]]
       ]

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case relates SUP sup sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TTop
