module Test.RunSpec (main, spec) where

import Test.Hspec

import Data.Bool             (bool)
import Text.Parsec           (eof, parse)

import Ceu.Eval              (Exp(..))
import Ceu.Grammar.Ann       (annz)
import Ceu.Grammar.Full.Eval (go, prelude)
import Ceu.Parser.Stmt       (stmt)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

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
            `shouldBe` Left "(line 1, column 1):\ntypes do not match : expected 'Bool' : found 'Int'\n"
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
                
