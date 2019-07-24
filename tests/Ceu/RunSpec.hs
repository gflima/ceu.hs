module Ceu.RunSpec (main, spec) where

import Test.Hspec
import Data.Bool             (bool)
import Debug.Trace
import Text.Parsec           (parse)

import Ceu.Eval              (Exp(..))
import Ceu.Grammar.Ann       (annz)
import Ceu.Grammar.Full.Eval (go, prelude)
import Ceu.Parser.Stmt       (prog)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    --describe "TODO:" $ do

    describe "return:" $ do
        it "return 1" $
            run True "return 1"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "return a" $
            run True "return a"
            `shouldBe` Left "(line 1, column 8):\nvariable 'a' is not declared\n"
        it "return ()" $
            run True "return ()"
            `shouldBe` Right EUnit

    describe "exps:" $ do
        it "return -1" $
            run True "return -1"
            `shouldBe` Right (EData ["Int","-1"] EUnit)
        it "return - (-1)" $
            run True "return - (-1)"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "return -( - 1)" $
            run True "return -(-  1)"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "return ((1))" $
            run True "return ((1))"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "return ((-9999))" $
            run True "return ((-9999))"
            `shouldBe` Right (EData ["Int","-9999"] EUnit)
        it "(1+2)*3" $
            run True "return (1+2)*3"
            `shouldBe` Right (EData ["Int","9"] EUnit)
        it "(1+2)*3" $
            run True "return (1+2)*3"
            `shouldBe` Right (EData ["Int","9"] EUnit)
        it "(1+2)-3" $
            run True "return (1+2)-3"
            `shouldBe` Right (EData ["Int","0"] EUnit)
        it "((1+2)*3)/4" $
            run True "return ((1+2)*3)/4"
            `shouldBe` Right (EData ["Int","2"] EUnit)
        it "+ (1 2)" $
            run True "return + (1,2)"
            `shouldBe` Right (EData ["Int","3"] EUnit)

    describe "vars:" $ do
        it "var Int a,b" $
            run True "var a,b :Int;" -- TODO: support a,b,c? (problem w/ assign/finalization)
            `shouldBe` Left "(line 1, column 6):\nunexpected \",\"\nexpecting identifier or \":\""
        it "a =  1; return a;" $
            run True "set a = 1; return a"
            `shouldBe` Left "(line 1, column 5):\nvariable 'a' is not declared\n(line 1, column 19):\nvariable 'a' is not declared\n"
        it "var a  : Int = 1; return a;" $
            run True "var a  : Int = 1; return a"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "var a:Int ; a = 1" $
            run True "var a :Int ; set a = 1 ; return a"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "var x :Int; x=1; return x" $
            run True "var x:Int; set x = 1 ;return x"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "hide a" $
            run True "var a :Int ; var a :Int ; return 0"
            `shouldBe` Left "(line 1, column 14):\nvariable 'a' is already declared\n"
        it "TODO-index-tuples" $
            run True "var x:(Int,()) = (1,()) ; var y:(Int,()) = x ; return 1"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "var x:(Int,Int) = (1,2) ; return '+ x | (TODO: no RT support for tuples)" $
            run True "var x:(Int,Int) = (1,2) ; return + x"
            `shouldBe` Right (EData ["Int","3"] EUnit)

-------------------------------------------------------------------------------

    describe "func:" $ do

      it "f1 ; return f1 1" $
        run True "func f1 () : (() -> Int) do return 1 end ; return f1()"
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "return 1+2" $
        run True "return 1+2"
        `shouldBe` Right (EData ["Int","3"] EUnit)

      it "return +(1,2)" $
        run True "return +(1,2)"
        `shouldBe` Right (EData ["Int","3"] EUnit)

      it "Int ; + ; return 1+2" $
        run False "data Int ; func + : ((Int,Int)->Int) ; return 1+2"
        `shouldBe` Right (EData ["Int","3"] EUnit)

      it "Int ; + ; return +(1,2)" $
        run False "data Int ; func + : ((Int,Int)->Int) ; return +(1,2)"
        `shouldBe` Right (EData ["Int","3"] EUnit)

      it "(f,g) = (+,c) ; return f(g 1, g 2)" $
        (run True $
          unlines [
            "func c (v) : (Int -> Int) do return v end",
            "var f : ((Int,Int) -> Int)",
            "var g : (Int -> Int)",
            "set (f,g) = (+,c)",
            "return f (g 1, g 2)"
           ])
        `shouldBe` Right (EData ["Int","3"] EUnit)

      it "glb = 1 ; f () -> glb ; ret glb" $
        (run True $
          unlines [
            "var glb : Int",
            "set glb = 1",
            "func f () : (() -> Int) do",
            "   return glb",
            "end",
            "return f()"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "glb = 1 ; f() -> g() -> glb ; ret f()()" $
        (run True $
          unlines [
            "var glb : Int = 1",
            "func f () : (() -> (() -> Int)) do",
            " return func () : (()->Int) do return glb end",
            "end",
            "return (f())()"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "call 1" $
        (run True $ "call 1")
        `shouldBe` Left "(line 1, column 1):\nexpected call\n"

      it "call print" $
        (run True $ "call print 1 ; return print 2")
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "recursion" $
        (run True $
          unlines [
            "func fat (v) : (Int -> Int) do",
            "   if v == 1 then",
            "     return 1",
            "   else",
            "     return v * (fat (v-1))",
            "   end",
            "end",
            "return fat 5"
           ])
        `shouldBe` Right (EData ["Int","120"] EUnit)

      it "dynamic scope" $
        (run True $
          unlines [
            "var a : Int = 0",
            "func f () : (() -> Int) do",
            "   return a",
            "end",
            "func g () : (() -> Int) do",
            "   var a : Int =10",
            "   return f()",        -- dynamic scope not possible b/c redefinitions are errors
            "end",
            "return g ()"
           ])
        `shouldBe` Left "(line 6, column 4):\nvariable 'a' is already declared\n"

      it "fst : (a,a) -> a" $
        (run True $
          unlines [
            "func fst (x,y) : ((a,a) -> a) do",
            "   return x",
            "end",
            "return fst (Bool.True, Bool.False)"
          ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "ret type" $
        (run True $
          unlines [
            "func f () : (() -> Int) do",
            "   return Bool.True",
            "end",
            "var v : Int = f()",
            "return v"
          ])
        `shouldBe` Left "(line 2, column 11):\ntypes do not match : expected 'Int' : found 'Bool.True'\n"

    describe "refs:" $ do

      it "y = &x" $
        (run True $
          unlines [
            "var x : Int     = 10",
            "var y : ref Int = ref x",
            "return y"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "y = &x ; x=10 ; ret y" $
        (run True $
          unlines [
            "var x : Int     = 0",
            "var y : ref Int = ref x",
            "set y = 10",
            "return x"
           ])
        `shouldBe` Left "10"

      it "ref - bad receive" $
        (run True $
          unlines [
            "func g x : (ref Int -> ()) do",
            "   return ()",
            "end",
            "return g (10)"
           ])
        `shouldBe` Left "(line 4, column 8):\ntypes do not match : expected '(Int -> ?)' : found '(ref Int -> ())'\n"

      it "y = &10" $
        (run True $
          unlines [
            "var y : ref Int = ref (10+10)",
            "return y"
           ])
        `shouldBe` Left "10"

      it "y = &10 ; y=5 ; ret y" $
        (run True $
          unlines [
            "var y : ref Int = ref 10",
            "set y = 5",
            "return y"
           ])
        `shouldBe` Left "TODO: ref should be constant"

    describe "closure:" $ do

      it "FuncGlobal pass" $
        (run True $
          unlines [
            "func g f : ((() -> Int) -> Int) do",
            "   return f()",
            "end",
            "var v : Int = 10",
            "return g (func () : (() -> Int) do return v end)"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "FuncNested pass" $
        (run True $
          unlines [
            "func g ((),f) : (((),(() -> Int)) -> Int) do",
            "   return f()",
            "end",
            "func h () : (() -> Int) do",
            " var v : Int = 10",
            " return g ((), func () : (() -> Int) do return v end)",
            "end",
            "return h()"
           ])
        `shouldBe` Left "(line 6, column 16):\ncannot pass nested function\n"

      it "FuncNested pass" $
        (run True $
          unlines [
            "func h () : (() -> Int) do",
            " func g ((),f) : (((),(() -> Int)) -> Int) do",
            "   return f()",
            " end",
            " var v : Int = 10",
            " return g ((), func () : (() -> Int) do return v end)",
            "end",
            "return h()"
           ])
        `shouldBe` Left "(line 6, column 16):\ncannot pass nested function\n"

      it "FuncNested pass" $
        (run True $
          unlines [
            "func h () : (() -> Int) do",
            " var v : Int = 10",
            " var g : (()->Int) = func () : (() -> Int) do return v end",
            " return g()",
            "end",
            "return h()"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "FuncGlobal return" $
        (run True $
          unlines [
            "var v : Int = 10",
            "func h () : (() -> (() -> Int)) do",
            " return func () : (() -> Int) do return v end",
            "end",
            "return (h())()"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "FuncNested return" $
        (run True $
          unlines [
            "func h () : (() -> (() -> Int)) do",
            " var v : Int = 10",
            " return func () : (() -> Int) do return v end",
            "end"
           ])
        `shouldBe` Left "(line 3, column 9):\ncannot return nested function\n"

      it "FuncGlobal return" $
        (run True $
          unlines [
            "func g () : (() -> (() -> Int)) do",
            "   return func () : (()->Int) do return 10 end",
            "end",
            "return (g ()) ()"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "FuncClosure return - not required" $
        (run True $
          unlines [
            "func g () : (() -> (() -> Int)) do",
            "   return new func () : (()->Int) do return 10 end",
            "end",
            "return (g ()) ()"
           ])
        `shouldBe` Left "new not required"

      it "FuncNested return - reference in body (not args)" $
        (run True $
          unlines [
            "func g x : (Int -> (() -> Int)) do",
            "   var ref a = x",
            "   return func () : (()->Int) do return a end",
            "end",
            "var a : Int = 99",
            "return (g ()) ()"
           ])
        `shouldBe` Left "TODO: cannot return"

      it "FuncClosure return - reference in args" $
        (run True $
          unlines [
            "func g x : (ref Int -> (() -> Int)) do",
            "   return func () : (()->Int) do return x end",
            "end",
            "var a : ref Int",
            "return (g (a)) ()"
           ])
        `shouldBe` Left "TODO: 99"

      it "escape scope - var a - func " $
        (run True $
          unlines [
            "func g () : (() -> (() -> Int)) do",
            "   var a : Int =10",
            "   return func () : (()->Int) do return a end",
            "end",
            "var a : Int = 99",
            "return (g ()) ()"
           ])
        `shouldBe` Left "new required"

      it "escape scope - var a - new func " $
        (run True $
          unlines [
            "func g () : (() -> (() -> Int)) do",
            "   var a : Int =10",
            "   return new func () : (()->Int) do return a end",
            "end",
            "var a : Int = 99",
            "return (g ()) ()"
           ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

    describe "data:" $ do

      it "data Xxx" $
        (run False "data Xxx ; var x:Xxx = Xxx ; return x")
        `shouldBe` Right (EData ["Xxx"] EUnit)

      it "data Xxx.Yyy" $
        (run False "data Xxx ; data Xxx.Yyy ; var x:Xxx.Yyy = Xxx.Yyy ; return x")
        `shouldBe` Right (EData ["Xxx","Yyy"] EUnit)

      it "data Xxx.Yyy" $
        (run False "data Xxx ; data Xxx.Yyy ; var x:Xxx = Xxx.Yyy ; return x")
        `shouldBe` Right (EData ["Xxx","Yyy"] EUnit)

      it "data Xxx with (Int,Int)" $
        (run True "data Xxx with (Int,Int) ; var x:Xxx = Xxx (1+1,2+2) ; return x")
        `shouldBe` Right (EData ["Xxx"] (ETuple [EData ["Int","2"] EUnit, EData ["Int","4"] EUnit]))

      it "data Xxx(Int), Xxx.Yyy(Int), y=Yyy(1,2)" $
        (run True "data Xxx with Int ; data Xxx.Yyy with Int ; var y:Xxx.Yyy = Xxx.Yyy (1,2) ; return y")
        `shouldBe` Right (EData ["Xxx","Yyy"] (ETuple [EData ["Int","1"] EUnit,EData ["Int","2"] EUnit]))

      it "Aa = Aa.Bb" $
        (run True $
          unlines [
            "data Aa with Int",
            "data Aa.Bb",
            "var b : Aa.Bb = Aa.Bb 1",
            "var a : Aa = b",
            "var v : Int",
            "set (Aa v) = b",
            "return v"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "List" $
        (run True $
          unlines [
            "data List",
            "data List.Pair with (Int,List)",
            "var l1 : List",
            "var l2 : List.Pair",
            "set l1 = l2",
            "return 1"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "List" $
        (run True $
          unlines [
            "data List",
            "data List.Empty",
            "data List.Pair with (Int,List)",
            "var l1 : List      = List",
            "var l2 : List.Pair = List.Pair(1, List.Empty)",
            "set l1  = l2",
            "set List = l2",
            "var x:Int",
            "set List.Pair (x,_) = l2",
            "return x"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "List" $
        (run True $
          unlines [
            "data List",
            "data List.Empty",
            "data List.Pair with (Int,List)",
            "var l1 : List = List.Pair(1, List.Empty)",
            "var x1 : Int",
            "set! List.Pair(x1,_) = l1",
            "return x1"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "Pair (a,b) = (1,2)" $
        (run True $
          unlines [
            "data Pair for (a,b) with (a,b)",
            "var p1 : Pair of (Int,Int) = Pair (1,2)",
            "return p1"
           ])
        `shouldBe` Right (EData ["Pair"] (ETuple [EData ["Int","1"] EUnit,EData ["Int","2"] EUnit]))

      it "Pair (a,b) =  1" $
        (run True $
          unlines [
            "data Pair for (a,b) with (a,b)",
            "var p1 : Pair of (Int,Int) =  1",
            "return p1"
           ])
        `shouldBe` Left "(line 2, column 31):\ntypes do not match : expected '(Pair of (Int,Int))' : found 'Int'\n"

      it "Pair (a,b) =  Pair 1" $
        (run True $
          unlines [
            "data Pair for (a,b) with (a,b)",
            "var p1 : Pair of (Int,Int) =  Pair 1",
            "return p1"
           ])
        `shouldBe` Left "(line 2, column 31):\ntypes do not match : expected '(Int -> (Pair of (Int,Int)))' : found '((a,b) -> (Pair of (a,b)))'\n"
                -- Left "(line 2, column 31):\ntypes do not match : expected '(a,b)' : found 'Int.1'\n"

      it "EUnit (a) ; p: EUnit Int" $
        (run True $
          unlines [
            "data EUnit for a with a",
            "var p1 : EUnit of Int",
            "return p1"
           ])
        `shouldBe` Right (EVar "p1")

      it "Pair (a,Int) ; p: Pair Int" $
        (run True $
          unlines [
            "data Pair for a with (a,Int)",
            "var p1 : Pair of Int",
            "return p1"
           ])
        `shouldBe` Right (EVar "p1")

      it "Pair (a,b) =  Pair (1,())" $
        (run True $
          unlines [
            "data Pair with (Int,Int)",
            "var p1 : Pair =  Pair (1,())",
            "return p1"
           ])
        `shouldBe` Left "(line 2, column 18):\ntypes do not match : expected '((Int,()) -> Pair)' : found '((Int,Int) -> Pair)'\n"
                -- Left "(line 2, column 18):\ntypes do not match : expected '(Int,Int)' : found '(Int.1,())'\n"

      it "Pair (a,b) =  Pair (1,())" $
        (run True $
          unlines [
            "data Pair for (a,b) with (a,b)",
            "var p1 : Pair of (Int,Int) =  Pair (1,())",
            "return p1"
           ])
        `shouldBe` Left "(line 2, column 31):\ntypes do not match : expected '((Int,()) -> (Pair of (Int,Int)))' : found '((a,b) -> (Pair of (a,b)))'\n(line 2, column 31):\nambiguous instances for 'b' : '()', 'Int'\n"

    describe "fields: index:" $ do

      it "One._1" $
        (run True $
          unlines [
            "return One._1 1"
           ])
        `shouldBe` Left "(line 1, column 8):\ndata 'One' is not declared\n"

      it "One._1" $
        (run True $
          unlines [
            "data One with (Int)",
            "var p1 : One = One 1",
            "return One._1 p1"
           ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "One._2" $
        (run True $
          unlines [
            "data One with (Int)",
            "var p1 : One = One 1",
            "return One._2 p1"
           ])
        `shouldBe` Left "(line 3, column 8):\nfield '_2' is not declared\n"

      it "One.Two._1" $
        (run True $
          unlines [
            "data Two with (Int,Int)",
            "data One with (Two)",
            "var p1 : One = One (Two (0,2))",
            "return Two._2 (One._1 p1)"
           ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "One.Two._2" $
        (run True $
          unlines [
            "data One     with (Int)",
            "data One.Two with (Int)",
            "var p1 : One.Two = One.Two (0,2)",
            "return One.Two._2 p1"
           ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "Pair (a,b) =  Pair (1,())" $
        (run True $
          unlines [
            "data Pair for (a,b) with (a,b)",
            "var p1 : Pair of (Int,()) =  Pair (1,())",
            "return Pair._2 p1"
           ])
        `shouldBe` Right EUnit

    describe "fields: names:" $ do

      it "One._1" $
        (run True $
          unlines [
            "return One.f 1"
           ])
        `shouldBe` Left "(line 1, column 8):\ndata 'One' is not declared\n"

      it "One._1" $
        (run True $
          unlines [
            "data One with (Int)",
            "var p1 : One = One 1",
            "return One.f p1"
           ])
        `shouldBe` Left "(line 3, column 8):\nfield 'f' is not declared\n"

      it "One._1" $
        (run True $
          unlines [
            "data One (f,g) with (Int)",
            "var p1 : One = One 1",
            "return One.f p1"
           ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "One._1" $
        (run True $
          unlines [
            "data One f with (Int)",
            "var p1 : One = One 1",
            "return One.f p1"
           ])
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "One._2" $
        (run True $
          unlines [
            "data One f with (Int)",
            "var p1 : One = One 1",
            "return One.g p1"
           ])
        `shouldBe` Left "(line 3, column 8):\nfield 'g' is not declared\n"

      it "One.Two._1" $
        (run True $
          unlines [
            "data Two (f,g) with (Int,Int)",
            "data One (t) with Two",
            "var p1 : One = One (Two (0,2))",
            "return Two.g (One.t p1)"
           ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "One.Two._2" $
        (run True $
          unlines [
            "data One     o with (Int)",
            "data One.Two t with (Int)",
            "var p1 : One.Two = One.Two (0,2)",
            "return One.Two.t p1"
           ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "Pair (a,b) =  Pair (1,())" $
        (run True $
          unlines [
            "data Pair (x,y) for (a,b) with (a,b)",
            "var p1 : Pair of (Int,()) =  Pair (1,())",
            "return Pair.y p1"
           ])
        `shouldBe` Right EUnit

    describe "match:" $ do

      it "1 = 1" $
        (run True "set 1 = 1 ; return 1")
        `shouldBe` Right (EData ["Int","1"] EUnit)
      it "1 = 2" $
        (run True "set 1 =  2 ; return 2")
        `shouldBe` Left "(line 1, column 5):\nmatch never succeeds : data mismatch\n"

      it "match 1 with ~x" $
        (run True "var x:Int =  1 ; match 1 with ~x ; return 1")
        `shouldBe` Left "(line 1, column 18):\nmatch is non exhaustive\n"
      it "match reduntant" $
        (run True "match 1 with case _ then case _ then end ; return 1")
        `shouldBe` Left "(line 1, column 31):\npattern is redundant\n"
      it "match reduntant" $
        (run True "match 1 with case 1 then case _ then end ; return 1")
        `shouldBe` Left "(line 1, column 31):\npattern is redundant\n"
      it "match reduntant" $
        (run True "match () with case () then case () then case _ then end ; return 1")
        `shouldBe` Left "(line 1, column 33):\npattern is redundant\n(line 1, column 46):\npattern is redundant\n"
      it "x1 = 1" $
        (run True "var x:Int = 1 ; match! 1 with ~x ; return 1")
        `shouldBe` Right (EData ["Int","1"] EUnit)
      it "x1 = 2" $
        (run True "var x:Int = 1 ; match! 2 with ~x ; return 2")
        `shouldBe` Right (EError (-2))
      it "1 = x" $
        (run True "var x:Int = 1 ; set! 1 = x ; return x")
        `shouldBe` Right (EData ["Int","1"] EUnit)

      it "data X with Int ; x:Int ; X x = X 1" $
        (run True "data Xxx with Int ; var x:Int ; set Xxx x = Xxx 1 ; return x")
        `shouldBe` Right (EData ["Int","1"] EUnit)
      it "data X with Int ; X 1 = X 1" $
        (run True "data Xxx with Int ; set Xxx 1 = Xxx 1 ; return 1")
        `shouldBe` Right (EData ["Int","1"] EUnit)
      it "data X with Int ; X 2 = X 1" $
        (run True "data Xxx with Int ; set Xxx 2 =  Xxx 1 ; return 1")
        `shouldBe` Left "(line 1, column 29):\nmatch never succeeds : data mismatch\n"

      it "x = (10,2) ; (i,2) = x" $
        (run True "data Xxx with (Int,Int) ; var x : Xxx = Xxx (10,2) ; var i : int ; set! Xxx (i,2) = x ; return i")
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "match/if" $
        (run True $
          unlines [
            "var x:Int = 10",
            "if x == 0 then",
            "   return 0",
            "else/if 10 matches x then",
            "   return x",
            "else",
            "   return 0",
            "end"
          ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "match/if" $
        (run True $
          unlines [
            "var (x,y) : (Bool,Bool)",
            "set (x,y) = (Bool.True, Bool.False)",
            "return (x,y) matches (Bool.True,Bool.False)"
          ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "if" $
        (run True $
          unlines [
            "if Bool.False then",
            "else",
            "end",
            "return 10"
          ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "if" $
        (run True $
          unlines [
            " if Bool.True then",
            "else",
            "end",
            "return 10"
          ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

    describe "constraint:" $ do

{-
$f3$(a -> Int)$ :: IF3able a => a -> Int   // Class/constraint

$f3$(Int -> Int)$ :: Int -> Int;           // Inst/cat3
$f3$(Int -> Int)$ :: Int -> Int :
  f3 = $f3$(Int -> Int)$                   // Inst/cat1
  ...

$f3$(Int -> Int)$ 10                       // EVar
-}
      it "Int ; IF3able a ; inst IF3able Int ; return f3 1" $
        (run True $
          unlines [
            "constraint IF3able for a with"       ,
            " var f3 : (a -> Int)"              ,
            "end"                               ,
            "instance of IF3able for Int with"   ,
            " func f3 (v) : (Int -> Int) do"    ,
            "   return v"                       ,
            " end"                              ,
            "end"                               ,
            "return f3(10)"
          ])
        `shouldBe` Right (EData ["Int","10"] EUnit)

      it "Int ; Bool ; IF2able a ; inst IF2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "constraint IF2able for a with"       ,
            " var f2 : (a -> Int)"              ,
            "end"                               ,
            "instance of IF2able for Bool with"  ,
            " func f2 (v) : (Bool -> Int) do"   ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IF2able for Int with"   ,
            " func f2 (v) : (Int -> Int) do"    ,
            "   return v+1"                     ,
            " end"                              ,
            "end"                               ,
            "var ret : Int = f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "Int ; Bool ; IF2able a ; inst IF2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "constraint (IF2able for a) with"    ,
            " var f2 : (a -> Int)"              ,
            "end"                               ,
            "instance of IF2able for Int with" ,
            " func f2 (v) : (Int -> Int) do"    ,
            "   return v+1"                     ,
            " end"                              ,
            "end"                               ,
            "instance of IF2able for Bool with",
            " func f2 (v) : (Bool -> Int) do"   ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "var ret : Int = f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (EData ["Int","2"] EUnit)

      it "IEqualable" $
        (run True $
          unlines [
            "constraint IEqualable for a with",
            "   func === : ((a,a) -> Bool)",
            "   func =/= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of IEqualable for Bool with",
            "   func === (x,y) : ((Bool,Bool) -> Bool) do",
            "     return x",
            "   end",
            "   func =/= (x,y) : ((Bool,Bool) -> Bool) do",
            "     return y",
            "   end",
            "end",
            "return ((Bool.True) === (Bool.True)) =/= Bool.False"
           ])
        `shouldBe` Right (EData ["Bool","False"] EUnit)

      it "IOrd extends IEq" $
        (run True $
          unlines [
            "constraint IEq for a with",
            "   func === : ((a,a) -> Bool)",
            "end",
            "",
            "constraint (IOrd for a) where (a is IEq) with",
            "   func =>= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of (IOrd for Bool) with",
            "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x === y end",
            "end",
            "",
            "return (Bool.True) =>= (Bool.False)"
          ])
        --`shouldBe` Left "(line 9, column 1):\ninstance 'IEq for Bool' is not declared\n(line 10, column 55):\nvariable '===' has no associated instance for data '((Bool,Bool) -> top)' in class 'IEq'\n"
        `shouldBe` Left "(line 9, column 1):\ninstance 'IEq for Bool' is not declared\n(line 9, column 1):\nmissing instance of '==='\n"

      it "IOrd extends IEq" $
        (run True $
          unlines [
            "constraint IOrd for a where (a is IEq) with",
            "   func =>= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of (IOrd for Bool) with",
            "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x end",
            "end",
            "",
            "return (Bool.True) =>= (Bool.False)"
          ])
        `shouldBe` Left "(line 1, column 1):\nconstraint 'IEq' is not declared\n(line 5, column 1):\ninstance 'IEq for Bool' is not declared\n"

      it "IOrd embeds IEq" $
        (run True $
          unlines [
            "constraint (IOrd for a) with",
            "   func =%= : ((a,a) -> Bool)",
            "   func =$= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of (IOrd for Bool) with",
            "   func =%= (x,y) : ((Bool,Bool) -> Bool) do return y end",
            "   func =$= (x,y) : ((Bool,Bool) -> Bool) do return x =%= y end",
            "end",
            "",
            "return (Bool.True) =$= (Bool.False)"
          ])
        `shouldBe` Right (EData ["Bool","False"] EUnit)

      it "IOrd extends IEq" $
        (run True $
          unlines [
            "constraint IEq for a with",
            "   func =%= : ((a,a) -> Bool)",
            "end",
            "",
            "constraint IOrd for a where (a is IEq) with",
            "   func =$= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of IEq for Bool with",
            "   func =%= (x,y) : ((Bool,Bool) -> Bool) do return y end",
            "end",
            "",
            "instance of (IOrd for Bool) with",
            "   func =$= (x,y) : ((Bool,Bool) -> Bool) do return x =%= y end",
            "end",
            "",
            "return (Bool.True) =$= (Bool.False)"
          ])
        `shouldBe` Right (EData ["Bool","False"] EUnit)

      it "f1" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f1 : (a -> Bool)",
            "end",
            "instance of IFable for Bool with",
            "   func f1 x : (Bool -> Bool) do return Bool.True end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "f1.x" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f1 : (a -> Bool)",
            "end",
            "instance of IFable for Bool with",
            "   func f1 x : (Bool -> Bool) do return x end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "f1 default" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f1 x : (a -> Bool) do return Bool.True end",
            "end",
            "instance of IFable for Bool with",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "f1/f2" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f2 :   (a -> Bool)",
            "   func f1 x : (a -> Bool) do return f2 x end",
            "end",
            "",
            "instance of IFable for Bool with",
            "   func f2 x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "f1/f2/f3" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f3 :   (a -> Bool)",
            "   func f2 x : (a -> Bool) do return f3 x end",
            "   func f1 x : (a -> Bool) do return f2 x end",
            "end",
            "",
            "instance of IFable for Bool with",
            "   func f3 x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "IFable f ; g a is IFable" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "func g x : (a -> Bool) where (a is IFable) do",
            "   return f x",   -- dont instantiate f bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "return (g (Bool.True))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Left "(line 9, column 9):\nvariable 'g' has no associated instance for '(Bool.True -> ?)'\n"

      it "IFable f ; g a is IFable" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "func g x : (a -> Bool) where (a is IFable) do",
            "   return f x",   -- dont instantiate f bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "instance of IFable for Bool with",
            "   func f x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "",
            "return (g (Bool.True))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "IFable f ; g a is IFable" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "instance of IFable for Bool with",
            "   func f x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "",
            "func g x : (a -> Bool) where (a is IFable) do",
            "   return f x",   -- dont instantiate f bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "return (g (Bool.True))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "IFable f1/f2/f3 ; g/h a is IFable" $
        (run True $
          unlines [
            "constraint IFable for a with",
            "   func f3 :   (a -> Bool)",
            "   func f2 x : (a -> Bool) do return f3 x end",
            "   func f1 x : (a -> Bool) do return f2 x end",
            "end",
            "",
            "func g x : (a -> Bool) where a is IFable do",
            "   return f1 x",   -- dont instantiate f1 bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "instance of IFable for Bool with",
            "   func f3 x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "",
            "func h x : (a -> Bool) where a is IFable do",
            "   return f1 x",
            "end",
            "",
            "func or (x,y) : ((Bool,Bool)->Bool) do",
            "   if x matches Bool.True then",
            "     return Bool.True",
            "   else",
            "     return y",
            "   end",
            "end",
            "",
            "return (g (Bool.True)) or (h (Bool.False))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "params" $
        (run True $
          unlines [
            "func not (x) : (Bool->Bool) do",
            "   if x matches Bool.True then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "",
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if x matches Bool.False then",
            "     return Bool.False",
            "   else",
            "     return y",
            "   end",
            "end",
            "",
            "constraint IEqualable for a with",
            "   func === (x,y) : ((a,a) -> Bool) do",
            "     if y matches x then",
            "       if x matches y then",
            "         return Bool.True",
            "       else",
            "         return Bool.False",
            "       end",
            "     else",
            "       return Bool.False",
            "     end",
            "   end",
            "   func =/= (x,y) : ((a,a) -> Bool) do",
            "     return not (x === y)",
            "   end",
            "end",
            "",
            "instance of IEqualable for b with",
            "end",
            "",
            "return (1===1) and (1=/=2)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "tuples" $
        (run True $
          pre ++ unlines [
            "func f : ((a,a) -> Bool) do",
            "   return Bool.True",
            "end",
            "return (1,2) f (1,1)"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "tuples" $
        (run True $
          pre ++ unlines [
            "instance of IEqualable for b with",
            "end",
            --"instance of IOrderable for (a,b) with",
            --"end",
            --"return (((1,1)===(1,1)) and ((1,2)=/=(1,1))) and ((1,2)@>(1,1))"
            "return (((1,1)===(1,1)) and ((1,2)=/=(1,1)))"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

    describe "extends" $ do

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "constraint IFa for a with end",
            --"instance of IFa for (a,b) where (a,b) is (IFa,IFa) with end",
            "constraint IFb for a where (a is IFa) with end",
            "instance of IFb for (a,b) where (a is IFb, b is IFb) with end",
            "return Bool.True"
           ])
        `shouldBe` Left "(line 3, column 1):\ninstance 'IFa for (a,b)' is not declared\n"

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "constraint IFa for a with end",
            "instance of IFa for (c,d) where (c is IFa, d is IFa) with end",
            "constraint IFb for e where (e is IFa) with end",
            "instance of IFb for (m,n) where (m is IFb, n is IFb) with end",
            "return Bool.True"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "constraint IFa for a with end",
            "instance of IFa for (c,d) where (c is IFa,d is IFa) with end",
            "constraint IFb for e where (e is IFa) with",
            "   func f v : (e->()) do end",
            "end",
            "instance of IFb for (m,n) where (m is IFb,n is IFb) with",
            "   func f v : ((m,n)->()) do end",
            "end",
            "return Bool.True"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "constraint IGt for a with",
            "   func gt : ((a,a) -> Int)",
            "end",
            "instance of IGt for Int with",
            "   func gt (x,y) : ((Int,Int) -> Int) do return 1 end",
            "end",
            "instance of IGt for (m,n) where (m is IGt,n is IGt) with",
            "   func gt ((x1,x2),(y1,y2)) : (((m,n),(m,n)) -> Int) do",
            "     return (gt(x1,y1)) + (gt(x2,y2))",
            "   end",
            "end",
            "func gt2 ((x1,x2),(y1,y2)) : (((m,n),(m,n)) -> Int) where (m is IGt,n is IGt) do",
            "  return (gt(x1,y1)) + (gt(x2,y2))",
            "end",
            "return Bool.True"
           ])
        `shouldBe` Right (EData ["Bool","True"] EUnit)

-------------------------------------------------------------------------------

    describe "do-end:" $ do
        it "do return 1 end" $
            run True "do return 1; end"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "do end return 1" $
            run True "do end return 1;"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "do do do do return 1 end end end end" $
            run True "do do do do return 1 end end end end"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "do do do do end end end end return 1" $
            run True "do do do; do end ; end end end ;return 1"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "do ... end" $ do
            run True "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end return 1"
            `shouldBe` Right (EData ["Int","1"] EUnit)

    describe "if-then-else/if-else" $ do
        it "if 0 then return 0 else return 1 end" $
            run True "if 0 then return 0 else return 1 end"
            `shouldBe` Left "(line 1, column 4):\ntypes do not match : expected 'Bool' : found 'Int'\n"
        it "if 0==1 then return 0 else return 1 end" $
            run True "if 0==1 then return 0 else return 1 end"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "if then (if then else end) end" $
            run True "if 1==1 then if 0==1 then return 999 else return 1 end ; end ; return 999; "
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "if then (if then end) else end" $
            run True "if 0==1 then ; if 0==1 then end ; else return 1 end ; return 999"
            `shouldBe` Right (EData ["Int","1"] EUnit)
        it "if 1==1 then a=1; a=2; if 1==1 then return a end end" $
            run True "if 1==1 then var a:Int =1 ; set a=2; if 1==1 then return a end end ; return 999"
            `shouldBe` Right (EData ["Int","2"] EUnit)
        it "if 0==1 then . else/if 1==1 then return 1 else ." $
            run True "if 0==1 then return 0 else/if 1==1 then return 1 else return 0 end"
            `shouldBe` Right (EData ["Int","1"] EUnit)

-------------------------------------------------------------------------------

    where
        run :: Bool -> String -> Either String Exp
        run withPrelude input =
            let v = parse prog "" input in
                case v of
                    (Right p) ->
                      case go $ bool Prelude.id (prelude annz) withPrelude $ p of
                        (Left errs) -> Left $ concatMap (\s->s++"\n") errs
                        (Right exp) -> Right exp
                    (Left  v') -> Left (show v')

        pre = unlines [
          "func not (x) : (Bool->Bool) do",
          "   if x matches Bool.True then",
          "     return Bool.False",
          "   else",
          "     return Bool.True",
          "   end",
          "end",
          "",
          "func and (x,y) : ((Bool,Bool)->Bool) do",
          "   if x matches Bool.False then",
          "     return Bool.False",
          "   else",
          "     return y",
          "   end",
          "end",
          "",
          "constraint IEqualable for a with",
          "   func === (x,y) : ((a,a) -> Bool) do",
          "     if y matches x then",
          "       if x matches y then",
          "         return Bool.True",
          "       else",
          "         return Bool.False",
          "       end",
          "     else",
          "       return Bool.False",
          "     end",
          "   end",
          "   func =/= (x,y) : ((a,a) -> Bool) do",
          "     return not (x === y)",
          "   end",
          "end"
         ]
