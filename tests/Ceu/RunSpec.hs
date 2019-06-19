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
            `shouldBe` Right (Number 1)
        it "return a" $
            run True "return a"
            `shouldBe` Left "(line 1, column 8):\nvariable 'a' is not declared\n"
        it "return ()" $
            run True "return ()"
            `shouldBe` Right Unit

    describe "exps:" $ do
        it "return -1" $
            run True "return -1"
            `shouldBe` Right (Number (-1))
        it "return - (-1)" $
            run True "return - (-1)"
            `shouldBe` Right (Number 1)
        it "return -( - 1)" $
            run True "return -(-  1)"
            `shouldBe` Right (Number 1)
        it "return ((1))" $
            run True "return ((1))"
            `shouldBe` Right (Number 1)
        it "return ((-9999))" $
            run True "return ((-9999))"
            `shouldBe` Right (Number (-9999))
        it "(1+2)*3" $
            run True "return (1+2)*3"
            `shouldBe` Right (Number 9)
        it "(1+2)*3" $
            run True "return (1+2)*3"
            `shouldBe` Right (Number 9)
        it "(1+2)-3" $
            run True "return (1+2)-3"
            `shouldBe` Right (Number 0)
        it "((1+2)*3)/4" $
            run True "return ((1+2)*3)/4"
            `shouldBe` Right (Number 2)
        it "+ (1 2)" $
            run True "return + (1,2)"
            `shouldBe` Right (Number 3)

    describe "vars:" $ do
        it "var Int a,b" $
            run True "var a,b :Int;" -- TODO: support a,b,c? (problem w/ assign/finalization)
            `shouldBe` Left "(line 1, column 6):\nunexpected \",\"\nexpecting identifier or \":\""
        it "a <- 1; return a;" $
            run True "set a <- 1; return a"
            `shouldBe` Left "(line 1, column 7):\nvariable 'a' is not declared\n(line 1, column 20):\nvariable 'a' is not declared\n"
        it "var a  : Int <- 1; return a;" $
            run True "var a  : Int <- 1; return a"
            `shouldBe` Right (Number 1)
        it "var a:Int ; a <- 1" $
            run True "var a :Int ; set a <- 1 ; return a"
            `shouldBe` Right (Number 1)
        it "var x :Int; x<-1; return x" $
            run True "var x:Int; set x <- 1 ;return x"
            `shouldBe` Right (Number 1)
        it "hide a" $
            run True "var a :Int ; var a :Int ; return 0"
            `shouldBe` Left "(line 1, column 14):\nvariable 'a' is already declared\n"
        it "TODO-index-tuples" $
            run True "var x:(Int,()) <- (1,()) ; var y:(Int,()) <- x ; return 1"
            `shouldBe` Right (Number 1)
        it "var x:(Int,Int) <- (1,2) ; return '+ x | (TODO: no RT support for tuples)" $
            run True "var x:(Int,Int) <- (1,2) ; return + x"
            `shouldBe` Right (Number 3)

-------------------------------------------------------------------------------

    describe "func:" $ do

      it "f1 ; return f1 1" $
        run True "func f1 () : (() -> Int) do return 1 end ; return f1()"
        `shouldBe` Right (Number 1)

      it "return 1+2" $
        run True "return 1+2"
        `shouldBe` Right (Number 3)

      it "return +(1,2)" $
        run True "return +(1,2)"
        `shouldBe` Right (Number 3)

      it "Int ; + ; return 1+2" $
        run False "data Int ; func + : ((Int,Int)->Int) ; return 1+2"
        `shouldBe` Right (Number 3)

      it "Int ; + ; return +(1,2)" $
        run False "data Int ; func + : ((Int,Int)->Int) ; return +(1,2)"
        `shouldBe` Right (Number 3)

      it "(f,g) <- (+,c) ; return f(g 1, g 2)" $
        (run True $
          unlines [
            "func c (v) : (Int -> Int) do return v end",
            "var f : ((Int,Int) -> Int)",
            "var g : (Int -> Int)",
            "set (f,g) <- (+,c)",
            "return f (g 1, g 2)"
           ])
        `shouldBe` Right (Number 3)

      it "glb <- 1 ; f () -> glb ; ret glb" $
        (run True $
          unlines [
            "var glb : Int",
            "set glb <- 1",
            "func f () : (() -> Int) do",
            "   return glb",
            "end",
            "return f()"
          ])
        `shouldBe` Right (Number 1)

      it "glb <- 1 ; f() -> g() -> glb ; ret f()()" $
        (run True $
          unlines [
            "var glb : Int <- 1",
            "func f () : (() -> (() -> Int)) do",
            " return func () : (()->Int) do return glb end",
            "end",
            "return (f())()"
          ])
        `shouldBe` Right (Number 1)

      it "call 1" $
        (run True $ "call 1")
        `shouldBe` Left "(line 1, column 1):\nexpected call\n"

      it "call print" $
        (run True $ "call print 1 ; return print 2")
        `shouldBe` Right (Number 2)

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
        `shouldBe` Right (Number 120)

      it "dynamic scope" $
        (run True $
          unlines [
            "var a : Int <- 0",
            "func f () : (() -> Int) do",
            "   return a",
            "end",
            "func g () : (() -> Int) do",
            "   var a : Int <-10",
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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

    describe "data:" $ do

      it "data Xxx" $
        (run False "data Xxx ; var x:Xxx <- Xxx ; return x")
        `shouldBe` Right (Cons ["Xxx"] Unit)

      it "data Xxx.Yyy" $
        (run False "data Xxx ; data Xxx.Yyy ; var x:Xxx.Yyy <- Xxx.Yyy ; return x")
        `shouldBe` Right (Cons ["Xxx","Yyy"] Unit)

      it "data Xxx.Yyy" $
        (run False "data Xxx ; data Xxx.Yyy ; var x:Xxx <- Xxx.Yyy ; return x")
        `shouldBe` Right (Cons ["Xxx","Yyy"] Unit)

      it "data Xxx with (Int,Int)" $
        (run True "data Xxx with (Int,Int) ; var x:Xxx <- Xxx (1+1,2+2) ; return x")
        `shouldBe` Right (Cons ["Xxx"] (Tuple [Number 2, Number 4]))

      it "data Xxx(Int), Xxx.Yyy(Int), y=Yyy(1,2)" $
        (run True "data Xxx with Int ; data Xxx.Yyy with Int ; var y:Xxx.Yyy <- Xxx.Yyy (1,2) ; return y")
        `shouldBe` Right (Cons ["Xxx","Yyy"] (Tuple [Number 1,Number 2]))

      it "Aa <- Aa.Bb" $
        (run True $
          unlines [
            "data Aa with Int",
            "data Aa.Bb",
            "var b : Aa.Bb <- Aa.Bb 1",
            "var a : Aa <- b",
            "var v : Int",
            "set (Aa v) <- b",
            "return v"
          ])
        `shouldBe` Right (Number 1)

      it "List" $
        (run True $
          unlines [
            "data List",
            "data List.Empty",
            "data List.Pair with (Int,List)",
            "var l1 : List      <- List",
            "var l2 : List.Pair <- List.Pair(1, List.Empty)",
            "set l1   <- l2",
            "set List <- l2",
            "var x:Int",
            "set List.Pair (x,_) <- l2",
            "return x"
          ])
        `shouldBe` Right (Number 1)

      it "List" $
        (run True $
          unlines [
            "data List",
            "data List.Empty",
            "data List.Pair with (Int,List)",
            "var l1 : List <- List.Pair(1, List.Empty)",
            "var x1 : Int",
            "set! List.Pair(x1,_) <- l1",
            "return x1"
          ])
        `shouldBe` Right (Number 1)

    describe "match:" $ do

      it "1 <- 1" $
        (run True "set 1 <- 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "1 <- 2" $
        (run True "set 1 <- 2 ; return 2")
        `shouldBe` Left "(line 1, column 7):\ntypes do not match : expected 'Int.1' : found 'Int.2'\n"

      it "x1 <- 1" $
        (run True "var x:Int <- 1 ; set `x´ <- 1 ; return 1")
        `shouldBe` Left "(line 1, column 26):\nmatch might fail\n"
      it "x1 <- 1" $
        (run True "var x:Int <- 1 ; set! `x´ <- 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "x1 <- 2" $
        (run True "var x:Int <- 1 ; set! `x´ <- 2 ; return 2")
        `shouldBe` Right (Error (-2))
      it "1 <- x" $
        (run True "var x:Int <- 1 ; set! 1 <- x ; return x")
        `shouldBe` Right (Number 1)

      it "data X with Int ; x:Int ; X x <- X 1" $
        (run True "data Xxx with Int ; var x:Int ; set Xxx x <- Xxx 1 ; return x")
        `shouldBe` Right (Number 1)
      it "data X with Int ; X 1 <- X 1" $
        (run True "data Xxx with Int ; set Xxx 1 <- Xxx 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "data X with Int ; X 2 <- X 1" $
        (run True "data Xxx with Int ; set Xxx 2 <- Xxx 1 ; return 1")
        `shouldBe` Left "(line 1, column 31):\ntypes do not match : expected 'Int.2' : found 'Int.1'\n"

      it "x <- (10,2) ; (i,2) <- x" $
        (run True "data Xxx with (Int,Int) ; var x : Xxx <- Xxx (10,2) ; var i : int ; set! Xxx (i,2) <- x ; return i")
        `shouldBe` Right (Number 10)

      it "match/if" $
        (run True $
          unlines [
            "var x:Int <- 10",
            "if x == 0 then",
            "   return 0",
            "else/if `x´ <- 10 then",
            "   return x",
            "else",
            "   return 0",
            "end"
          ])
        `shouldBe` Right (Number 10)

      it "if" $
        (run True $
          unlines [
            "if Bool.False then",
            "else",
            "end",
            "return 10"
          ])
        `shouldBe` Right (Number 10)

      it "if" $
        (run True $
          unlines [
            " if Bool.True then",
            "else",
            "end",
            "return 10"
          ])
        `shouldBe` Right (Number 10)

    describe "interface:" $ do

{-
$f3$(a -> Int)$ :: IF3able a => a -> Int   // Class/constraint

$f3$(Int -> Int)$ :: Int -> Int;           // Inst/cat3
$f3$(Int -> Int)$ :: Int -> Int :
  f3 = $f3$(Int -> Int)$                   // Inst/cat1
  ...

$f3$(Int -> Int)$ 10                       // Read
-}
      it "Int ; IF3able a ; inst IF3able Int ; return f3 1" $
        (run True $
          unlines [
            "interface IF3able for a with"       ,
            " var f3 : (a -> Int)"              ,
            "end"                               ,
            "instance of IF3able for Int with"   ,
            " func f3 (v) : (Int -> Int) do"    ,
            "   return v"                       ,
            " end"                              ,
            "end"                               ,
            "return f3(10)"
          ])
        `shouldBe` Right (Number 10)

      it "Int ; Bool ; IF2able a ; inst IF2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "interface IF2able for a with"       ,
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
            "var ret : Int <- f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (Number 2)

      it "Int ; Bool ; IF2able a ; inst IF2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "interface (IF2able for a) with"    ,
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
            "var ret : Int <- f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (Number 2)

      it "IEqualable" $
        (run True $
          unlines [
            "interface IEqualable for a with",
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
        `shouldBe` Right (Cons ["Bool","False"] Unit)

      it "IOrd extends IEq" $
        (run True $
          unlines [
            "interface IEq for a with",
            "   func === : ((a,a) -> Bool)",
            "end",
            "",
            "interface (IOrd for a) extends (IEq for a) with",
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
            "interface (IOrd for a) extends (IEq for a) with",
            "   func =>= : ((a,a) -> Bool)",
            "end",
            "",
            "instance of (IOrd for Bool) with",
            "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x end",
            "end",
            "",
            "return (Bool.True) =>= (Bool.False)"
          ])
        `shouldBe` Left "(line 1, column 1):\ninterface 'IEq' is not declared\n(line 5, column 1):\ninstance 'IEq for Bool' is not declared\n"

      it "IOrd embeds IEq" $
        (run True $
          unlines [
            "interface (IOrd for a) with",
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
        `shouldBe` Right (Cons ["Bool","False"] Unit)

      it "IOrd extends IEq" $
        (run True $
          unlines [
            "interface IEq for a with",
            "   func =%= : ((a,a) -> Bool)",
            "end",
            "",
            "interface (IOrd for a) extends (IEq for a) with",
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
        `shouldBe` Right (Cons ["Bool","False"] Unit)

      it "f1" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f1 : (a -> Bool)",
            "end",
            "instance of IFable for Bool with",
            "   func f1 x : (Bool -> Bool) do return Bool.True end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "f1.x" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f1 : (a -> Bool)",
            "end",
            "instance of IFable for Bool with",
            "   func f1 x : (Bool -> Bool) do return x end",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "f1 default" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f1 x : (a -> Bool) do return Bool.True end",
            "end",
            "instance of IFable for Bool with",
            "end",
            "return f1 (Bool.True)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "f1/f2" $
        (run True $
          unlines [
            "interface IFable for a with",
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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "f1/f2/f3" $
        (run True $
          unlines [
            "interface IFable for a with",
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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IFable f ; g a implements IFable" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "func g x : (a -> Bool) where a implements IFable do",
            "   return f x",   -- dont instantiate f bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "return (g (Bool.True))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Left "(line 9, column 9):\nvariable 'g' has no associated instance for '(Bool.True -> ?)'\n"

      it "IFable f ; g a implements IFable" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "func g x : (a -> Bool) where a implements IFable do",
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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IFable f ; g a implements IFable" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f : (a -> Bool)",
            "end",
            "",
            "instance of IFable for Bool with",
            "   func f x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "",
            "func g x : (a -> Bool) where a implements IFable do",
            "   return f x",   -- dont instantiate f bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "return (g (Bool.True))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IFable f1/f2/f3 ; g/h a implements IFable" $
        (run True $
          unlines [
            "interface IFable for a with",
            "   func f3 :   (a -> Bool)",
            "   func f2 x : (a -> Bool) do return f3 x end",
            "   func f1 x : (a -> Bool) do return f2 x end",
            "end",
            "",
            "func g x : (a -> Bool) where a implements IFable do",
            "   return f1 x",   -- dont instantiate f1 bc typeof(x)=a and a is IFable
            "end",  -- declare one g for each instance
            "",
            "instance of IFable for Bool with",
            "   func f3 x : (Bool -> Bool) do",
            "     return x",
            "   end",
            "end",
            "",
            "func h x : (a -> Bool) where a implements IFable do",
            "   return f1 x",
            "end",
            "",
            "func or (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.True",
            "   else",
            "     return y",
            "   end",
            "end",
            "",
            "return (g (Bool.True)) or (h (Bool.False))"
                    -- g_Bool->Bool
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "params" $
        (run True $
          unlines [
            "func not (x) : (Bool->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "",
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.False <- x then",
            "     return Bool.False",
            "   else",
            "     return y",
            "   end",
            "end",
            "",
            "interface IEqualable for a with",
            "   func === (x,y) : ((a,a) -> Bool) do",
            "     if `x´ <- y then",
            "       if `y´ <- x then",
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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "tuples" $
        (run True $
          pre ++ unlines [
            "func f : ((a,a) -> Bool) do",
            "   return Bool.True",
            "end",
            "return (1,2) f (1,1)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

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
        `shouldBe` Right (Cons ["Bool","True"] Unit)

    describe "extends" $ do

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "interface IFa for a with end",
            --"instance of IFa for (a,b) where (a,b) implements (IFa,IFa) with end",
            "interface (IFb for a) extends (IFa for a) with end",
            "instance of IFb for (a,b) where (a,b) implements (IFb,IFb) with end",
            "return Bool.True"
           ])
        `shouldBe` Left "(line 3, column 1):\ninstance 'IFa for (a,b)' is not declared\n"

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "interface IFa for a with end",
            "instance of IFa for (c,d) where (c,d) implements (IFa,IFa) with end",
            "interface (IFb for e) extends (IFa for e) with end",
            "instance of IFb for (m,n) where (m,n) implements (IFb,IFb) with end",
            "return Bool.True"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "interface IFa for a with end",
            "instance of IFa for (c,d) where (c,d) implements (IFa,IFa) with end",
            "interface (IFb for e) extends (IFa for e) with",
            "   func f v : (e->()) do end",
            "end",
            "instance of IFb for (m,n) where (m,n) implements (IFb,IFb) with",
            "   func f v : ((m,n)->()) do end",
            "end",
            "return Bool.True"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "instance for extends of (a,b)" $
        (run True $
          unlines [
            "interface IGt for a with",
            "   func gt : ((a,a) -> Int)",
            "end",
            "instance of IGt for Int with",
            "   func gt (x,y) : ((Int,Int) -> Int) do return 1 end",
            "end",
            "instance of IGt for (m,n) where (m,n) implements (IGt,IGt) with",
            "   func gt ((x1,x2),(y1,y2)) : (((m,n),(m,n)) -> Int) do",
            "     return (gt(x1,y1)) + (gt(x2,y2))",
            "   end",
            "end",
            "func gt2 ((x1,x2),(y1,y2)) : (((m,n),(m,n)) -> Int) where (m,n) implements (IGt,IGt) do",
            "  return (gt(x1,y1)) + (gt(x2,y2))",
            "end",
            "return Bool.True"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

-------------------------------------------------------------------------------

    describe "do-end:" $ do
        it "do return 1 end" $
            run True "do return 1; end"
            `shouldBe` Right (Number 1)
        it "do end return 1" $
            run True "do end return 1;"
            `shouldBe` Right (Number 1)
        it "do do do do return 1 end end end end" $
            run True "do do do do return 1 end end end end"
            `shouldBe` Right (Number 1)
        it "do do do do end end end end return 1" $
            run True "do do do; do end ; end end end ;return 1"
            `shouldBe` Right (Number 1)
        it "do ... end" $ do
            run True "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end return 1"
            `shouldBe` Right (Number 1)

    describe "if-then-else/if-else" $ do
        it "if 0 then return 0 else return 1 end" $
            run True "if 0 then return 0 else return 1 end"
            `shouldBe` Left "(line 1, column 1):\ntypes do not match : expected 'Bool' : found 'Int.0'\n"
        it "if 0==1 then return 0 else return 1 end" $
            run True "if 0==1 then return 0 else return 1 end"
            `shouldBe` Right (Number 1)
        it "if then (if then else end) end" $
            run True "if 1==1 then if 0==1 then return 999 else return 1 end ; end ; return 999; "
            `shouldBe` Right (Number 1)
        it "if then (if then end) else end" $
            run True "if 0==1 then ; if 0==1 then end ; else return 1 end ; return 999"
            `shouldBe` Right (Number 1)
        it "if 1==1 then a=1; a=2; if 1==1 then return a end end" $
            run True "if 1==1 then var a:Int <-1 ; set a<-2; if 1==1 then return a end end ; return 999"
            `shouldBe` Right (Number 2)
        it "if 0==1 then . else/if 1==1 then return 1 else ." $
            run True "if 0==1 then return 0 else/if 1==1 then return 1 else return 0 end"
            `shouldBe` Right (Number 1)

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
          "   if Bool.True <- x then",
          "     return Bool.False",
          "   else",
          "     return Bool.True",
          "   end",
          "end",
          "",
          "func and (x,y) : ((Bool,Bool)->Bool) do",
          "   if Bool.False <- x then",
          "     return Bool.False",
          "   else",
          "     return y",
          "   end",
          "end",
          "",
          "interface IEqualable for a with",
          "   func === (x,y) : ((a,a) -> Bool) do",
          "     if `x´ <- y then",
          "       if `y´ <- x then",
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
