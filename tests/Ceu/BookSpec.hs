module Ceu.BookSpec (main, spec) where

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

-------------------------------------------------------------------------------

    -- TODO-3-20: square : Float -> Float

    describe "Chapter 1:" $ do

      it "square" $
        (run True $
          unlines [
            "func square (x) : (Int -> Int) do",
            "   return x * x",
            "end",
            "return square 3"
           ])
        `shouldBe` Right (Number 9)

      it "smaller" $
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

      it "square/smaller" $
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

      it "three" $
        (run True $
          unlines [
            "func three (x) : (Int -> Int) do",
            "   return 3",
            "end",
            "return three 10"
           ])
        `shouldBe` Right (Number 3)

      it "infinity" $
        (run True $
          unlines [
            "func infinity () : (() -> Int) do",
            "   return (infinity()) + 1",
            "end",
            "return infinity ()"
           ])
        `shouldBe` Right (Error (-1))

      it "three" $
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

      it "multiply 3 4" $
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

      it "multiply 3 infinity" $
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

      it "twice" $
        (run True $
          unlines [
            "func twice (f,x) : (((Int->Int), Int) -> Int) do",
            "   return f (f x)",
            "end",
            "return twice (negate,3)"
           ])
        `shouldBe` Right (Number 3)

      it "+" $
        (run True $
          unlines [
            "return 1 + (+ (2,3))"
           ])
        `shouldBe` Right (Number 6)

      it "signum" $
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

      it "fact" $
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

      it "fact - error" $
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

      it "locals" $
        (run True $
          unlines [
            "func f (x,y) : ((Int,Int)->Int) do",
            "   var a:Int <- x+y",
            "   return (a+1) * (a+2)",
            "end",
            "return f (2,3)"
           ])
        `shouldBe` Right (Number 42)

      it "locals" $
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

      it "not" $
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

      it "and-1" $
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

      it "and-2" $
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
            "return (Bool.True) and (Bool.True)"
           ])
        `shouldBe` Right (Cons ["Bool","True"] Unit)

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
