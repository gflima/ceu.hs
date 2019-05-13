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
            "interface IEqualable for a with",
            "   func ===       : ((a,a) -> Bool)",
            "   func =/= (x,y) : ((a,a) -> Bool) do return not (x === y) end",
            "end",
            "",
            "implementation of IEqualable for Bool with",
            "   func === (x,y) : ((Bool,Bool) -> Bool) do",
            "     return (x and y) or ((not x) and (not y))",
            "   end",
            "end",
            "return ((Bool.True) === (Bool.True)) =/= Bool.False"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "IOrderable" $        -- pg 32
        (run True $
          ord ++ unlines [
            "return ((((Bool.True)  @>  (Bool.False))  and ((Bool.True) @>= (Bool.True))) and",
            "         ((Bool.False) @<= (Bool.False))) and ((Bool.False) @< (Bool.True))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "@<=" $
        (run True $
          ord ++ unlines [
            "data Xx",
            "data Xx.Aa",
            "data Xx.Bb",
            "return (Xx.Aa) @<= (Xx.Bb)"
           ])
        `shouldBe` Left "(line 78, column 16):\nvariable '@<=' has no associated implementation for '((Xx.Aa,Xx.Bb) -> ?)'\n"

      it "leap years" $         -- pg 33
        (run True $
          ord ++ unlines [
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
          ord ++ unlines [
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
          ord ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "implementation of IEqualable for Triangle with",
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
          ord ++ unlines [
            "func impl (x,y) : ((Bool,Bool) -> Bool) do",
            " return (not x) or y",
            "end",
            "return (((impl (Bool.False,Bool.True)) and (impl (Bool.True,Bool.True)))",
            "  and (impl (Bool.False,Bool.False))) and (not (impl (Bool.True,Bool.False)))"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

      it "analyse triangles" $         -- pg 35
        (run True $
          ord ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "implementation of IEqualable for Triangle with",
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
          ord ++ unlines [
            "data Triangle",
            "data Triangle.Failure",
            "data Triangle.Isosceles",
            "data Triangle.Equilateral",
            "data Triangle.Scalene",
            "",
            "implementation of IEqualable for Triangle with",
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

      it "XXX: char" $         -- pg 36
        (run True $
          ord ++ unlines [
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
            "implementation of IEqualable for Char with",
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
            "implementation of IOrderable for Char with",
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

        ord = unlines [
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
          "implementation of IEqualable for Int with",
          "   func === (x,y) : ((Int,Int) -> Bool) do",
          "     return x == y",
          "   end",
          "end",
          "",
          "implementation of IEqualable for Bool with",
          "   func === (x,y) : ((Bool,Bool) -> Bool) do",
          "     return (x and y) or ((not x) and (not y))",
          "   end",
          "end",
          "",
          "interface IOrderable for a extends IEqualable for a with",
          "  func @<        : ((a,a) -> Bool)",
          "  func @<= (x,y) : ((a,a) -> Bool) do return (x @< y) or (x === y) end",
          "  func @>  (x,y) : ((a,a) -> Bool) do return not (x @<= y)         end",
          "  func @>= (x,y) : ((a,a) -> Bool) do return (x @> y) or (x === y) end",
          "end",
          "",
          "implementation of IOrderable for Int with",
          "  func @< (x,y) : ((Int,Int) -> Bool) do",
          "    return x < y",
          "  end",
          "end",
          "",
          "implementation of IOrderable for Bool with",
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

