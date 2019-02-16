module Ceu.RunSpec (main, spec) where

import Test.Hspec
import Data.Bool             (bool)
import Debug.Trace
import Text.Parsec           (eof, parse)

import Ceu.Eval              (Exp(..))
import Ceu.Grammar.Ann       (annz)
import Ceu.Grammar.Full.Eval (go, prelude)
import Ceu.Parser.Stmt       (stmt)

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
            `shouldBe` Left "(line 1, column 6):\nunexpected \",\"\nexpecting digit, letter, \"_\" or \":\""
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
        run False "type Int ; func + : ((Int,Int)->Int) ; return 1+2"
        `shouldBe` Right (Number 3)

      it "Int ; + ; return +(1,2)" $
        run False "type Int ; func + : ((Int,Int)->Int) ; return +(1,2)"
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

    describe "data:" $ do

      it "type Xxx" $
        (run False "type Xxx ; var x:Xxx <- Xxx ; return x")
        `shouldBe` Right (Cons ["Xxx"] Unit)

      it "type Xxx.Yyy" $
        (run False "type Xxx ; type Xxx.Yyy ; var x:Xxx.Yyy <- Xxx.Yyy ; return x")
        `shouldBe` Right (Cons ["Xxx","Yyy"] Unit)

      it "type Xxx.Yyy" $
        (run False "type Xxx ; type Xxx.Yyy ; var x:Xxx <- Xxx.Yyy ; return x")
        `shouldBe` Right (Cons ["Xxx","Yyy"] Unit)

      it "type Xxx with (Int,Int)" $
        (run True "type Xxx with (Int,Int) ; var x:Xxx <- Xxx (1+1,2+2) ; return x")
        `shouldBe` Right (Cons ["Xxx"] (Tuple [Number 2, Number 4]))

      it "type Xxx(Int), Xxx.Yyy(Int), y=Yyy(1,2)" $
        (run True "type Xxx with Int ; type Xxx.Yyy with Int ; var y:Xxx.Yyy <- Xxx.Yyy (1,2) ; return y")
        `shouldBe` Right (Cons ["Xxx","Yyy"] (Tuple [Number 1,Number 2]))

      it "Aa <- Aa.Bb" $
        (run True $
          unlines [
            "type Aa with Int",
            "type Aa.Bb",
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
            "type List",
            "type List.Empty",
            "type List.Pair with (Int,List)",
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
            "type List",
            "type List.Empty",
            "type List.Pair with (Int,List)",
            "var l1 : List <- List.Pair(1, List.Empty)",
            "var x1 : Int",
            "set! List.Pair(x1,_) <- l1",
            "return x1"
          ])
        `shouldBe` Right (Number 1)

    describe "assignment:" $ do

      it "1 <- 1" $
        (run True "set 1 <- 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "1 <- 2" $
        (run True "set 1 <- 2 ; return 2")
        `shouldBe` Left "(line 1, column 7):\ntypes do not match : expected 'Int.1' : found 'Int.2'\n"

      it "x1 <- 1" $
        (run True "var x:Int <- 1 ; set `x` <- 1 ; return 1")
        `shouldBe` Left "match might fail\n"
      it "x1 <- 1" $
        (run True "var x:Int <- 1 ; set! `x` <- 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "x1 <- 2" $
        (run True "var x:Int <- 1 ; set! `x` <- 2 ; return 2")
        `shouldBe` Right (Error 1)
      it "1 <- x" $
        (run True "var x:Int <- 1 ; set! 1 <- x ; return x")
        `shouldBe` Right (Number 1)

      it "data X with Int ; x:Int ; X x <- X 1" $
        (run True "type Xxx with Int ; var x:Int ; set Xxx x <- Xxx 1 ; return x")
        `shouldBe` Right (Number 1)
      it "data X with Int ; X 1 <- X 1" $
        (run True "type Xxx with Int ; set Xxx 1 <- Xxx 1 ; return 1")
        `shouldBe` Right (Number 1)
      it "data X with Int ; X 2 <- X 1" $
        (run True "type Xxx with Int ; set Xxx 2 <- Xxx 1 ; return 1")
        `shouldBe` Left "(line 1, column 31):\ntypes do not match : expected 'Int.2' : found 'Int.1'\n"

    describe "typeclass:" $ do

      it "Int ; F3able a ; inst F3able Int ; return f3 1" $
        (run True $
          unlines [
            "typeclass F3able for a with"       ,
            " var f3 : (a -> Int)"              ,
            "end"                               ,
            "instance of F3able for Int with"   ,
            " func f3 (v) : (Int -> Int) do"    ,
            "   return v"                       ,
            " end"                              ,
            "end"                               ,
            "return f3(10)"
          ])
        `shouldBe` Right (Number 10)

      it "Int ; Bool ; F2able a ; inst F2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "typeclass F2able for a with"       ,
            " var f2 : (a -> Int)"              ,
            "end"                               ,
            "instance of F2able for Bool with"  ,
            " func f2 (v) : (Bool -> Int) do"   ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of F2able for Int with"   ,
            " func f2 (v) : (Int -> Int) do"    ,
            "   return v+1"                     ,
            " end"                              ,
            "end"                               ,
            "var ret : Int <- f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (Number 2)

      it "Int ; Bool ; F2able a ; inst F2able Bool/Int ; return f2 1" $
        (run True $
          unlines [
            "typeclass F2able for a with"       ,
            " var f2 : (a -> Int)"              ,
            "end"                               ,
            "instance of F2able for Int with"   ,
            " func f2 (v) : (Int -> Int) do"    ,
            "   return v+1"                     ,
            " end"                              ,
            "end"                               ,
            "instance of F2able for Bool with"  ,
            " func f2 (v) : (Bool -> Int) do"   ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "var ret : Int <- f2(1)"            ,
            "return ret"
          ])
        `shouldBe` Right (Number 2)

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
            `shouldBe` Left "(line 1, column 1):\ntypes do not match : expected 'Bool.True' : found 'Int.0'\n"
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
            let v = parse (stmt <* eof) "" input in
                case v of
                    (Right p) ->
                      case go $ bool Prelude.id (prelude annz) withPrelude $ p of
                        (Left errs) -> Left $ concatMap (\s->s++"\n") errs
                        (Right exp) -> Right exp
                    (Left  v') -> Left (show v')
