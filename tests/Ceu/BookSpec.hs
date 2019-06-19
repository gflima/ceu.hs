module Ceu.BookSpec (main, spec) where

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

-------------------------------------------------------------------------------

    -- TODO-3-20: square : Float -> Float

    describe "Chapter 1:" $ do

      it "square" $           -- pg 2
        (run True $
          unlines [
            "func square (x) : (Int -> Int) do",
            "   return x * x",
            "end",
            "return square 3"
           ])
        `shouldBe` Right (Number 9)

      it "smaller" $          -- pg 2
        (run True $
          unlines [
            "func smaller (x,y) : ((Int,Int) -> Int) do",
            "   if x <= y then",
            "     return x",
            "   else",
            "     return y",
            "   end",
            "end",
            "return (smaller(10,5)) + (smaller(1,4))"
           ])
        `shouldBe` Right (Number 6)

      it "square/smaller" $   -- pg 3
        (run True $
          unlines [
            "func square (x) : (Int -> Int) do",
            "   return x * x",
            "end",
            "func smaller (x,y) : ((Int,Int) -> Int) do",
            "   if x <= y then",
            "     return x",
            "   else",
            "     return y",
            "   end",
            "end",
            "return square (smaller (5, 3+4))"
           ])
        `shouldBe` Right (Number 25)

      -- TODO-3

      it "three" $            -- pg 5
        (run True $
          unlines [
            "func three (x) : (Int -> Int) do",
            "   return 3",
            "end",
            "return three 10"
           ])
        `shouldBe` Right (Number 3)

      it "infinity" $         -- pg 5
        (run True $
          unlines [
            "func infinity () : (() -> Int) do",
            "   return (infinity()) + 1",
            "end",
            "return infinity ()"
           ])
        `shouldBe` Right (Error (-1))

      it "three/infinity" $   -- pg 5
        (run True $
          unlines [
            "func three (x) : (Int -> Int) do",
            "   return 3",
            "end",
            "func infinity () : (() -> Int) do",
            "   return (infinity()) + 1",
            "end",
            "return three (infinity ())"
           ])
        `shouldBe` Right (Error (-1))

      it "multiply 3 4" $     -- pg 9
        (run True $
          unlines [
            "func multiply (x,y) : ((Int,Int) -> Int) do",
            "   if x == 0 then",
            "     return 0",
            "   else",
            "     return x * y",
            "   end",
            "end",
            "return multiply (3,4)"
           ])
        `shouldBe` Right (Number 12)

      it "multiply 3 infinity" $  -- pg 9
        (run True $
          unlines [
            "func multiply (x,y) : ((Int,Int) -> Int) do",
            "   if x == 0 then",
            "     return 0",
            "   else",
            "     return x * y",
            "   end",
            "end",
            "func infinity () : (() -> Int) do",
            "   return (infinity()) + 1",
            "end",
            "return multiply (3,infinity())"
           ])
        `shouldBe` Right (Error (-1))

      it "twice" $            -- pg 12
        (run True $
          unlines [
            "func twice (f,x) : (((Int->Int), Int) -> Int) do",
            "   return f (f x)",
            "end",
            "return twice (negate,3)"
           ])
        `shouldBe` Right (Number 3)

      it "+" $                -- pg 12
        (run True $
          unlines [
            "return 1 + (+ (2,3))"
           ])
        `shouldBe` Right (Number 6)

      it "signum" $           -- pg 18
        (run True $
          unlines [
            "func signum (x) : (Int->Int) do",
            "   if x < 0 then",
            "     return  -1",
            "   else/if x == 0 then",
            "     return 0",
            "   else",
            "     return 1",
            "   end",
            "end",
            "return (signum 1) + ((signum (-10)) + (signum (10-10)))"
           ])
        `shouldBe` Right (Number 0)

      it "fact" $             -- pg 19
        (run True $
          unlines [
            "func fact (n) : (Int->Int) do",
            "   if n == 0 then",
            "     return 1",
            "   else",
            "     return n * (fact (n-1))",
            "   end",
            "end",
            "return fact 5"
           ])
        `shouldBe` Right (Number 120)

      it "fact - error" $     -- pg 20
        (run True $
          unlines [
            "func fact (n) : (Int->Int) do",
            "   if n < 0 then",
            "     error 1",
            "   else/if n == 0 then",
            "     return 1",
            "   else",
            "     return n * (fact (n-1))",
            "   end",
            "end",
            "return fact (-5)"
           ])
        `shouldBe` Right (Error 1)

      it "locals" $           -- pg 20
        (run True $
          unlines [
            "func f (x,y) : ((Int,Int)->Int) do",
            "   var a:Int <- x+y",
            "   return (a+1) * (a+2)",
            "end",
            "return f (2,3)"
           ])
        `shouldBe` Right (Number 42)

      it "locals" $           -- pg 21
        (run True $
          unlines [
            "func f (x,y) : ((Int,Int)->Int) do",
            "   var (a,b):(Int,Int) <- (x+y, x*y)",
            "   return (a+1) * (b+2)",
            "end",
            "return f (2,3)"
           ])
        `shouldBe` Right (Number 48)

      -- TODO-20

    describe "Chapter 2:" $ do

      it "data" $             -- pg 29
        (run True $
          unlines [
            "data Bool_",
            "data Bool_.False_",
            "data Bool_.True_",
            "return Bool_.True_"
          ])
        `shouldBe` Right (Cons ["Bool_","True_"] Unit)

      it "not" $              -- pg 30
        (run True $
          unlines [
            "func not (x) : (Bool->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "return not Bool.False"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "and-1" $            -- pg 30
        (run True $
          unlines [
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.False <- x then",
            "     return Bool.False",
            "   else/if Bool.False <- y then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "return and (Bool.True,Bool.False)"
           ])
        `shouldBe` Right (Cons ["Bool","False"] Unit)

      it "and-2" $            -- pg 30
        (run True $
          unlines [
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.False <- x then",
            "     return Bool.False",
            "   else",
            "     return y",
            "   end",
            "end",
            "return (Bool.True) and (Bool.True)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "or" $               -- pg 30
        (run True $
          unlines [
            "func or (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.True",
            "   else",
            "     return y",
            "   end",
            "end",
            "return (Bool.True) or (Bool.False)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "===, =/=" $         -- pg 31
        (run True $
          unlines [
            "func not (x) : (Bool->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.False <- x then",
            "     return Bool.False",
            "   else",
            "     return y",
            "   end",
            "end",
            "func or (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.True",
            "   else",
            "     return y",
            "   end",
            "end",
            "func === (x,y) : ((Bool,Bool)->Bool) do",
            "   return (x and y) or ((not x) and (not y))",
            "end",
            "func =/= (x,y) : ((Bool,Bool)->Bool) do",
            "   return not (x === y)",
            "end",
            "return ((Bool.True) === (Bool.True)) =/= Bool.False"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IEqualable: default =/=" $   -- pg 32
        (run True $
          unlines [
            "func not (x) : (Bool->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.False",
            "   else",
            "     return Bool.True",
            "   end",
            "end",
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.False <- x then",
            "     return Bool.False",
            "   else",
            "     return y",
            "   end",
            "end",
            "func or (x,y) : ((Bool,Bool)->Bool) do",
            "   if Bool.True <- x then",
            "     return Bool.True",
            "   else",
            "     return y",
            "   end",
            "end",
            "",
            "constraint IEqualable for a with",
            "   func ===       : ((a,a) -> Bool)",
            "   func =/= (x,y) : ((a,a) -> Bool) do return not (x === y) end",
            "end",
            "",
            "instance of IEqualable for Bool with",
            "   func === (x,y) : ((Bool,Bool) -> Bool) do",
            "     return (x and y) or ((not x) and (not y))",
            "   end",
            "end",
            "return ((Bool.True) === (Bool.True)) =/= Bool.False"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IOrderable" $        -- pg 32
        (run True $
          pre ++ unlines [
            "return ((((Bool.True)  @>  (Bool.False))  and ((Bool.True) @>= (Bool.True))) and",
            "         ((Bool.False) @<= (Bool.False))) and ((Bool.False) @< (Bool.True))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "@<=" $
        (run True $
          pre ++ unlines [
            "data Xx",
            "data Xx.Aa",
            "data Xx.Bb",
            "return (Xx.Aa) @<= (Xx.Bb)"
           ])
        `shouldBe` Left "(line 78, column 16):\nvariable '@<=' has no associated instance for '((Xx.Aa,Xx.Bb) -> ?)'\n"

      it "leap years" $         -- pg 33
        (run True $
          pre ++ unlines [
            "func leapyear (y) : (Int -> Bool) do",
            "   if (y rem 100) == 0 then",
            "     return (y rem 400) == 0",
            "   else",
            "     return (y rem 4) == 0",
            "   end",
            "end",
            "return (((not (leapyear 1979)) and (leapyear 1980)) and (not (leapyear 100))) and (leapyear 400)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "analyse triangles" $         -- pg 33
        (run True $
          pre ++ unlines [
            "func analyse (x,y,z) : ((Int,Int,Int) -> Int) do",
            "   if (x + y) <= z then",
            "     return 0",  -- Fail
            "   else/if x == z then",
            "     return 1",  -- Equi
            "   else/if (x == y) or (y == z) then",
            "     return 2",  -- Isos
            "   else",
            "     return 3",  -- Scal
            "   end",
            "end",
            "return ((((analyse (10,20,30)) == 0) and ((analyse (10,20,25)) == 3))",
            "   and ((analyse (10,20,20)) == 2)) and ((analyse (10,10,10)) == 1)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "analyse triangles" $         -- pg 33
        (run True $
          pre ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "instance of IEqualable for Triangle with",
            "end",
            "",
            "func analyse (x,y,z) : ((Int,Int,Int) -> Triangle) do",
            "   if (x + y) @<= z then",
            "     return Triangle.Failure",
            "   else/if x === z then",
            "     return Triangle.Equilateral",
            "   else/if (x === y) or (y === z) then",
            "     return Triangle.Isosceles",
            "   else",
            "     return Triangle.Scalene",
            "   end",
            "end",
            "return ((((analyse (10,20,30)) === (Triangle.Failure)) and ((analyse (10,20,25)) === (Triangle.Scalene)))",
            "   and ((analyse (10,20,20)) === (Triangle.Isosceles))) and ((analyse (10,10,10)) === (Triangle.Equilateral))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "implication" $         -- pg 34
        (run True $
          pre ++ unlines [
            "func impl (x,y) : ((Bool,Bool) -> Bool) do",
            " return (not x) or y",
            "end",
            "return (((impl (Bool.False,Bool.True)) and (impl (Bool.True,Bool.True)))",
            "  and (impl (Bool.False,Bool.False))) and (not (impl (Bool.True,Bool.False)))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "analyse triangles" $         -- pg 35
        (run True $
          pre ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "instance of IEqualable for Triangle with",
            "end",
            "",
            "func analyse (x,y,z) : ((Int,Int,Int) -> Triangle) do",
            "   if (x + y) @<= z then",
            "     return Triangle.Failure",
            "   else/if x === z then",
            "     return Triangle.Equilateral",
            "   else/if (x === y) or (y === z) then",
            "     return Triangle.Isosceles",
            "   else",
            "     return Triangle.Scalene",
            "   end",
            "end",
            "",
            "func analyse2 (x,y,z) : ((Int,Int,Int) -> Triangle) do",
            "   if (x @<= y) and (x @<= z) then",
            "     if y @<= z then",
            "       return analyse(x,y,z)",
            "     else",
            "       return analyse(x,z,y)",
            "     end",
            "   else/if (y @<= x) and (y @< z) then",
            "     if x @<= z then",
            "       return analyse(y,x,z)",
            "     else",
            "       return analyse(y,z,x)",
            "     end",
            "   else",
            "     if x @<= y then",
            "       return analyse(z,x,y)",
            "     else",
            "       return analyse(z,y,x)",
            "     end",
            "   end",
            "end",
            "return ((((analyse2 (30,20,10)) === (Triangle.Failure)) and ((analyse2 (10,25,20)) === (Triangle.Scalene)))",
            "   and ((analyse2 (10,20,20)) === (Triangle.Isosceles))) and ((analyse2 (10,10,10)) === (Triangle.Equilateral))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "sort3" $         -- pg 35
        (run True $
          pre ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "instance of IEqualable for Triangle with",
            "end",
            "",
            "func analyse (x,y,z) : ((Int,Int,Int) -> Triangle) do",
            "   if (x + y) @<= z then",
            "     return Triangle.Failure",
            "   else/if x === z then",
            "     return Triangle.Equilateral",
            "   else/if (x === y) or (y === z) then",
            "     return Triangle.Isosceles",
            "   else",
            "     return Triangle.Scalene",
            "   end",
            "end",
            "",
            "func sort3 (x,y,z) : ((Int,Int,Int) -> (Int,Int,Int)) do",
            "   if (x @<= y) and (x @<= z) then",
            "     if y @<= z then",
            "       return (x,y,z)",
            "     else",
            "       return (x,z,y)",
            "     end",
            "   else/if (y @<= x) and (y @< z) then",
            "     if x @<= z then",
            "       return (y,x,z)",
            "     else",
            "       return (y,z,x)",
            "     end",
            "   else",
            "     if x @<= y then",
            "       return (z,x,y)",
            "     else",
            "       return (z,y,x)",
            "     end",
            "   end",
            "end",
            "",
            "return ((((analyse (sort3 (30,20,10))) === (Triangle.Failure))  and",
            "         ((analyse (sort3 (10,25,20))) === (Triangle.Scalene))) and",
            "         ((analyse (sort3 (10,20,20))) === (Triangle.Isosceles))) and",
            "         ((analyse (sort3 (10,10,10))) === (Triangle.Equilateral))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "char" $         -- pg 36
        (run True $
          pre ++ unlines [
            "data Char",
            "data Char.AA",
            "data Char.BB",
            "data Char.CC",
            "data Char.DD",
            "data Char.Aa",
            "data Char.Bb",
            "data Char.Cc",
            "data Char.Dd",
            "",
            "instance of IEqualable for Char with",
            "end",
            "",
            "func ord c : (Char -> Int) do",
            " if c === Char.AA then",
            "   return 1",
            " else/if c === Char.BB then",
            "   return 2",
            " else/if c === Char.CC then",
            "   return 3",
            " else/if c === Char.DD then",
            "   return 4",
            " else/if c === Char.Aa then",
            "   return 11",
            " else/if c === Char.Bb then",
            "   return 12",
            " else/if c === Char.Cc then",
            "   return 13",
            " else/if c === Char.Dd then",
            "   return 14",
            " else",
            "   return 0",
            " end",
            "end",
            "",
            "func chr c : (Int -> Char) do",
            " if c === 1 then",
            "   return Char.AA",
            " else/if c === 2 then",
            "   return Char.BB",
            " else/if c === 3 then",
            "   return Char.CC",
            " else/if c === 4 then",
            "   return Char.DD",
            " else/if c === 11 then",
            "   return Char.Aa",
            " else/if c ===  12then",
            "   return Char.Bb",
            " else/if c === 13 then",
            "   return Char.Cc",
            " else/if c === 14 then",
            "   return Char.Dd",
            " else",
            "   return 0",
            " end",
            "end",
            "",
            "instance of IOrderable for Char with",
            "  func @< (x,y) : ((Char,Char) -> Bool) do",
            "    return (ord x) < (ord y)",
            "  end",
            "end",
            "",
            "func isLower c : (Char -> Bool) do",
            "   return (c @>= Char.Aa) and (c @<= Char.Dd)",
            "end",
            "",
            "func capitalize c : (Char -> Char) do",
            "   var off : Int <- (ord (Char.AA)) - (ord (Char.Aa))",
            "   if isLower c then",
            "     return chr (off + (ord c))",
            "   else",
            "     return c",
            "   end",
            "end",
            "",
            "func nextlet c : (Char -> Char) do",
            "   var (min,max) : (Int,Int)",
            "   if isLower c then",
            "     set (min,max) <- (ord Char.Aa, ord Char.Dd)",
            "   else",
            "     set (min,max) <- (ord Char.AA, ord Char.DD)",
            "   end",
            "   return chr (((((ord c) - min) + 1) rem ((max-min)+1)) + min)",
            "end",
            "",
            "var c1 : Char <- Char.AA",
            "var c2 : Char <- Char.BB",
            "",
            "var eq  : Bool <- c1 =/= c2",
            "var gt  : Bool <- c1 @< c2",
            "var cs  : Bool <- (Char.AA) @< (Char.Aa)",
            "var low : Bool <- (not (isLower (Char.AA))) and (isLower (Char.Dd))",
            "var cp1 : Bool <- (capitalize (Char.BB)) === (Char.BB)",
            "var cp2 : Bool <- (capitalize (Char.Cc)) === (Char.CC)",
            "var nx1 : Bool <- (nextlet (Char.Cc)) === (Char.Dd)",
            "var nx2 : Bool <- (nextlet (Char.AA)) === (Char.BB)",
            "var nx3 : Bool <- (nextlet (Char.DD)) === (Char.AA)",
            "var nx4 : Bool <- (nextlet (Char.Dd)) === (Char.Aa)",
            "var nx  : Bool <- (nx1 and nx2) and (nx3 and nx4)",
            "var sum : Int  <- (((ord c1) + (ord c2)) + (ord (Char.CC))) + (ord (Char.DD))",
            "return (((((eq and gt) and cs) and low) and (cp1 and cp2)) and nx) and (sum == 10)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "enum" $         -- pg 38
        (run True $
          pre ++ unlines [
            "constraint IEnumerable for a with",
            "   func toEnum   : (a -> Int)",
            "   func fromEnum : (Int -> a)",
            "end",
            "",
            "data Day",
            "data Day.Sun",
            "data Day.Mon",
            "data Day.Tue",
            "data Day.Wed",
            "data Day.Thu",
            "data Day.Fri",
            "data Day.Sat",
            "",
            "instance of IEqualable for Day with end",
            "",
            "instance of IEnumerable for Day with",
            "   func toEnum day : (Day -> Int) do",
            "     if day === Day.Sun then",
            "       return 0",
            "     else/if day === Day.Mon then",
            "       return 1",
            "     else/if day === Day.Tue then",
            "       return 2",
            "     else/if day === Day.Wed then",
            "       return 3",
            "     else/if day === Day.Thu then",
            "       return 4",
            "     else/if day === Day.Fri then",
            "       return 5",
            "     else/if day === Day.Sat then",
            "       return 6",
            "     end",
            "   end",
            "",
            "   func fromEnum int : (Int -> Day) do",
            "     if int === 0 then",
            "       return Day.Sun",
            "     else/if int === 1 then",
            "       return Day.Mon",
            "     else/if int === 2 then",
            "       return Day.Tue",
            "     else/if int === 3 then",
            "       return Day.Wed",
            "     else/if int === 4 then",
            "       return Day.Thu",
            "     else/if int === 5 then",
            "       return Day.Fri",
            "     else/if int === 6 then",
            "       return Day.Sat",
            "     end",
            "   end",
            "end",
            "",
            "instance of IOrderable for Day with",
            "  func @< (x,y) : ((Day,Day) -> Bool) do",
            "    return (toEnum x) < (toEnum y)",
            "  end",
            "end",
            "",
            "func workday (day) : (Day -> Bool) do",
            "  return (day @>= (Day.Mon)) and (day @<= (Day.Fri))",
            "end",
            "",
            "func dayAfter (day) : (Day -> Day) do",
            "  return fromEnum (((toEnum day) + 1) rem 7)",
            "end",
            "",
            "var d1 : Day <- Day.Sun",
            "var d2 : Day <- Day.Mon",
            "",
            "var eq  : Bool <- d1 =/= d2",
            "var gt  : Bool <- d1 @< d2",
            "var wd1 : Bool <- workday (Day.Sun)",
            "var wd2 : Bool <- workday (Day.Fri)",
            "var aft : Bool <- ((dayAfter (Day.Sun)) === (Day.Mon)) and ((dayAfter (Day.Sat)) === (Day.Sun))",
            "var sum : Int  <- (((toEnum d1) + (toEnum d2)) + (toEnum (Day.Sat))) + (toEnum (Day.Wed))",
            "return ((((eq and gt) and (sum == 10)) and ((fromEnum(toEnum(Day.Sat))) === Day.Sat)) and ((not wd1) and wd2)) and aft"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "direction" $         -- pg 41
        (run True $
          pre ++ unlines [
            "constraint IEnumerable for a with",
            "   func toEnum   : (a -> Int)",
            "   func fromEnum : (Int -> a)",
            "end",
            "",
            "data Dir",
            "data Dir.N",
            "data Dir.S",
            "data Dir.L",
            "data Dir.O",
            "",
            "instance of IEqualable for Dir with end",
            "",
            "instance of IEnumerable for Dir with",
            "   func toEnum dir : (Dir -> Int) do",
            "     if dir === Dir.N then",
            "       return 0",
            "     else/if dir === Dir.S then",
            "       return 1",
            "     else/if dir === Dir.L then",
            "       return 2",
            "     else/if dir === Dir.O then",
            "       return 3",
            "     end",
            "   end",
            "",
            "   func fromEnum int : (Int -> Dir) do",
            "     if int === 0 then",
            "       return Dir.N",
            "     else/if int === 1 then",
            "       return Dir.S",
            "     else/if int === 2 then",
            "       return Dir.L",
            "     else/if int === 3 then",
            "       return Dir.O",
            "     end",
            "   end",
            "end",
            "",
            "func reverse (dir) : (Dir -> Dir) do",
            "   if dir === (Dir.N) then",
            "     return Dir.S",
            "   else/if dir === (Dir.S) then",
            "     return Dir.N",
            "   else/if dir === (Dir.L) then",
            "     return Dir.O",
            "   else/if dir === (Dir.O) then",
            "     return Dir.L",
            "   end",
            "end",
            "",
            "return (reverse (Dir.O)) === (Dir.L)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "bool enum" $         -- pg 41
        (run True $
          pre ++ unlines [
            "constraint IEnumerable for a with",
            "   func toEnum   : (a -> Int)",
            "   func fromEnum : (Int -> a)",
            "end",
            "",
            "instance of IEnumerable for Bool with",
            "   func toEnum bool : (Bool -> Int) do",
            "     if bool === (Bool.False) then",
            "       return 0",
            "     else/if bool === (Bool.True) then",
            "       return 1",
            "     end",
            "   end",
            "",
            "   func fromEnum int : (Int -> Bool) do",
            "     if int === 0 then",
            "       return Bool.False",
            "     else/if int === 1 then",
            "       return Bool.True",
            "     end",
            "   end",
            "end",
            "",
            "return fromEnum ((toEnum (Bool.False)) + 1)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "XXX: TODO: mkpair" $         -- pg 41
        (run True $
          pre ++ unlines [
            "data Pair with (a,b)",
            "var Pair p1 : Pair (Int,Int) <- Pair (1,2)",
            "return p1"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "fst/snd" $         -- pg 41
        (run True $
          pre ++ unlines [
            "func fst (x,y) : ((a,b) -> a) do",
            "   return x",
            "end",
            "func snd (_,y) : ((a,b) -> a) do",
            "   return y",
            "end",
            "return (((fst (1,-1)) + (snd (1,-1))) === 0) and (snd (Bool.False, Bool.True))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "pair" $         -- pg 42
        (run True $
          pre ++ unlines [
            "func pair ((f,g), x) : ((((a->b),(a->c)),a) -> (b,c)) do",
            "   return (f x, g x)",
            "end",
            "func f x : (Int -> Bool) do",
            "   return (x rem 2) === 1",
            "end",
            "func g x : (Int -> Int) do",
            "   return x * 2",
            "end",
            "return pair ((f,g), 3)"
           ])
        `shouldBe` Right (Tuple [Cons ["Bool","True"] Unit,Number 6])

      it "TODO: compose" $         -- pg 42
        (run True $
          pre ++ unlines [
            "func compose (f,g) : (((a->b),(b->c)) -> (a -> c)) do",
            "   return func x : (a -> c) do",
            "           return f (g x)",
            "          end",
            "end",
            "func inc x : (Int -> Int) do",
            "   return x+1",
            "end",
            "func dec x : (Int -> Int) do",
            "   return x-1",
            "end",
            "func dup x : (Int -> Int) do",
            "   return x*2",
            "end",
            "return (compose (dec, compose(dup,inc))) 10"
           ])
        `shouldBe` Right (Number 21)

      it "cross" $         -- pg 42
        (run True $
          pre ++ unlines [
            "func fst (x,y) : ((a,b) -> a) do",
            "   return x",
            "end",
            "func snd (_,y) : ((a,b) -> a) do",
            "   return y",
            "end",
            "func cross ((f,g), p) : ((((a->b),(c->d)),(a,c)) -> (b,d)) do",
            "   return (f (fst p), g (snd p))",
            "end",
            "func f x : (Int -> Bool) do",
            "   return (x rem 2) === 1",
            "end",
            "func g x : (Int -> Int) do",
            "   return x * 2",
            "end",
            "return cross ((f,g), (3,4))"
           ])
        `shouldBe` Right (Tuple [Cons ["Bool","True"] Unit,Number 8])

      it "pi" $         -- pg 44
        (run True $
          pre ++ unlines [
            "func pifun : (() -> Int) do",
            "   return 314",
            "end",
            "return pifun ()"
           ])
        `shouldBe` Right (Number 314)

      it "roots" $         -- pg 44
        (run True $
          pre ++ unlines [
            "instance of IEqualable for (Int,Int) with end",
            "func sqrt x : (Int -> Int) do",
            "  if (x === 0) or (x === 1) then",
            "    return x; ",
            "  end",
            "",
            "  var i : Int <- 1",
            "  var r : Int <- 1",
            "  loop do",
            "    if r @> x then",
            "      return i - 1",
            "    else",
            "      set i <- i + 1",
            "      set r <- i * i",
            "    end",
            "  end",
            "end",
            "func roots (a,b,c) : ((Int,Int,Int) -> (Int,Int)) do",
            "   var e : Int <- (b*b) - (4 * (a*c))",
            "   if a === 0 then",
            "     return (0,0)",
            "   else/if e @< 0 then",
            "     return (-1,-1)",
            "   else",
            "     var d : Int <- 2 * a",
            "     var r : Int <- sqrt e",
            "     return (((-b)-r)/d, ((-b)+r)/d)",
            "   end",
            "end",
            "return (((roots (3,4,5)) === (-1,-1)) and ((roots (2,-16,-18)) === (-1,9))) and ((roots (0,1,1)) === (0,0))",
            "//return (roots (2,-16,-18))",
            ""
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "tuples / eq" $         -- pg 45
        (run True $
          pre ++ unlines [
            "instance of IEqualable for (a,b) with end",
            "return (((1,1)===(1,1)) and ((1,2)=/=(1,1)))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "tuples / ord" $         -- pg 45
        (run True $
          pre ++ unlines [
            "instance of IEqualable for (a,b) with end",
            "instance of IOrderable for (a,b) where (a is IOrderable,b is IOrderable) with",
            "   func @< ((i,j),(x,y)) : (((a,b),(a,b)) -> Bool) do",
            "     return (i @< x) or ((i === x) and (j @< y))",
            "   end",
            "end",
            "return ((1,1) === (1,1)) and (((1,1) @< (1,2)) and ((1,2) @< (2,1)))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

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
          "func and (x,y) : ((Bool,Bool)->Bool) do",
          "   if Bool.False <- x then",
          "     return Bool.False",
          "   else",
          "     return y",
          "   end",
          "end",
          "func or (x,y) : ((Bool,Bool)->Bool) do",
          "   if Bool.True <- x then",
          "     return Bool.True",
          "   else",
          "     return y",
          "   end",
          "end",
          "",
          "constraint IEqualable for a with",
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
          "instance of IEqualable for Int with",
          "   func === (x,y) : ((Int,Int) -> Bool) do",
          "     return x == y",
          "   end",
          "end",
          "",
          "instance of IEqualable for Bool with",
          "   func === (x,y) : ((Bool,Bool) -> Bool) do",
          "     return (x and y) or ((not x) and (not y))",
          "   end",
          "end",
          "",
          "constraint IOrderable for a where (a is IEqualable) with",
          "  func @<        : ((a,a) -> Bool)",
          "  func @<= (x,y) : ((a,a) -> Bool) do return (x @< y) or (x === y) end",
          "  func @>  (x,y) : ((a,a) -> Bool) do return not (x @<= y)         end",
          "  func @>= (x,y) : ((a,a) -> Bool) do return (x @> y) or (x === y) end",
          "end",
          "",
          "instance of IOrderable for Int with",
          "  func @< (x,y) : ((Int,Int) -> Bool) do",
          "    return x < y",
          "  end",
          "end",
          "",
          "instance of IOrderable for Bool with",
          "  func @< (x,y) : ((Bool,Bool) -> Bool) do",
          "    if      (Bool.False, Bool.False) <- (x, y) then return Bool.False",
          "    else/if (Bool.False, Bool.True)  <- (x, y) then return Bool.True",
          "    else/if (Bool.True,  Bool.False) <- (x, y) then return Bool.False",
          "    else/if (Bool.True,  Bool.True)  <- (x, y) then return Bool.False",
          "    end",
          "  end",
          "end",
          ""
         ]
