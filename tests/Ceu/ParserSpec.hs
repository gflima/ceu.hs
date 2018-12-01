module Test.ParserSpec (main, spec) where

import Test.Hspec

import Text.Parsec.Prim
import Text.Parsec.String (Parser)
import FunctionsAndTypesForParsing

import Ceu.Parser.Token
import Ceu.Parser.Exp
import Ceu.Parser.Stmt
import Ceu.Grammar.Globals (Exp(..))
import Ceu.Grammar.Full.Grammar (Stmt(..))

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "TODO:" $ do

    describe "tokens:" $ do
        describe "tk_str:" $ do
            it "(" $
                parse (tk_str "(") "( "
                `shouldBe` Right ()
            it ")" $
                parse (tk_str ")") ") "
                `shouldBe` Right ()
            it "-" $
                parse (tk_str "-") "- "
                `shouldBe` Right ()
        describe "tk_num:" $ do
            it "''" $
                parse (s>>tk_num) "\n "
                `shouldBe` Left "(line 2, column 2):\nunexpected end of input\nexpecting digit"
            it "''" $
                parse tk_num ""
                `shouldBe` Left "(line 1, column 1):\nunexpected end of input\nexpecting digit"
            it "1" $
                parse tk_num "1"
                `shouldBe` Right 1
            it "10" $
                parse tk_num "10"
                `shouldBe` Right 10
            it "a" $
                parse tk_num "a"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"a\"\nexpecting digit"
        describe "tk_var:" $ do
            it "''" $
                parse (s>>tk_var) "\n "
                `shouldBe` Left "(line 2, column 2):\nunexpected end of input"
            it "''" $
                parse tk_var ""
                `shouldBe` Left "(line 1, column 1):\nunexpected end of input"
            it "id" $
                parse tk_var "id"
                `shouldBe` Right "id"
            it "1" $
                parse tk_var "1"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"1\""
            it "var" $
                parse tk_var "var"
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting digit, letter or \"_\""
        describe "tk_int:" $ do
            it "''" $
                parse (s>>tk_int) "\n "
                `shouldBe` Left "(line 2, column 2):\nunexpected end of input"
            it "''" $
                parse tk_int ""
                `shouldBe` Left "(line 1, column 1):\nunexpected end of input"
            it "id" $
                parse tk_int "id"
                `shouldBe` Right "id"
            it "1" $
                parse tk_int "1"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"1\""
            it "var" $
                parse tk_int "var"
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting digit, letter or \"_\""

        describe "tk_key:" $ do
            it "do" $
                parse (tk_key "do") "do "
                `shouldBe` Right ()
            it "end" $
                parse (tk_key "end") "end"
                `shouldBe` Right ()
            it "escape" $
                parse (tk_key "escape") "escape\n"
                `shouldBe` Right ()

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_const "0"
                `shouldBe` Right (Const 0)
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Read "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Read "aaa")
        describe "umn:" $ do
            it "-1" $
                parse expr_umn "-1"
                `shouldBe` Right (Umn (Const 1))
            it "--1" $
                parse expr_umn "--1"
                `shouldBe` Right (Umn (Umn (Const 1)))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (Const 1)
            it "((--1))" $
                parse expr_parens "((--1))"
                `shouldBe` Right (Umn (Umn (Const 1)))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr_add_sub "1+1"
                `shouldBe` Right (Add (Const 1) (Const 1))
            it "1+2+3" $
                parse expr_add_sub "1 + 2+3"
                `shouldBe` Right (Add (Add (Const 1) (Const 2)) (Const 3))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr_mul_div "1*1"
                `shouldBe` Right (Mul (Const 1) (Const 1))
            it "1*2*3" $
                parse expr_mul_div "1 * 2*3"
                `shouldBe` Right (Mul (Mul (Const 1) (Const 2)) (Const 3))
        describe "expr:" $ do
            it "0" $
                parse expr "0"
                `shouldBe` Right (Const 0)
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Read "aaa")
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Umn (Const 1))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (Read "aaa")
            it "1+2-3" $
                parse expr "1+2-3"
                `shouldBe` Right (Sub (Add (Const 1) (Const 2)) (Const 3))
            it "1+2*3" $
                parse expr "1+2*3"
                `shouldBe` Right (Add (Const 1) (Mul (Const 2) (Const 3)))
            it "1+2*3/4" $
                parse expr "1+2*3/4"
                `shouldBe` Right (Add (Const 1) (Div (Mul (Const 2) (Const 3)) (Const 4)))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Mul (Add (Const 1) (Const 2)) (Const 3))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right Nop

        describe "escape:" $ do
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape Nothing (Just (Const 0)))
            it "escape aaa" $
                parse stmt_escape "escape aaa"
                `shouldBe` Right (Escape Nothing (Just (Read "aaa")))

        describe "do-end:" $ do
            it "do escape 1 end" $
                parse stmt_do "do escape 1 end"
                `shouldBe` Right (Scope (Escape Nothing (Just (Const 1))))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse (tk_key "do" >> (try stmt_escape <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (Scope Nop)

        describe "seq:" $ do
            it "do end; escape 1" $
                parse stmt_seq "do end escape 1"
                `shouldBe` Right (Seq (Scope Nop) (Escape Nothing (Just (Const 1))))

        describe "var:" $ do
            it "var int x" $
                parse stmt_var "var int x;"
                `shouldBe` Right (Var "x" Nothing Nothing)
            it "var var x" $
                parse stmt_var "var var x"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "var int a <- 1" $
                parse stmt_var "var int a <- 1"
                `shouldBe` Right (Var "a" (Just (Const 1)) Nothing)

        describe "write:" $ do
            it "x <- 1" $
                parse stmt_write "x <- 1"
                `shouldBe` Right (Write "x" (Const 1))
            it "var <- 1" $
                parse stmt_write "var <- 1"
                `shouldBe` Left "(line 1, column 4):\nunexpected \" \"\nexpecting digit, letter or \"_\""

        describe "if-then-else" $ do
            it "if 0 then escape 0" $
                parse stmt_if "if 0 then escape"
                `shouldBe` Left "(line 1, column 11):\nunexpected \"s\"\nexpecting \"end\""

            it "if 0 escape 0 end" $
                parse stmt_if "if 0 escape 0 end"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"e\"\nexpecting \"*\", \"/\", \"+\", \"-\" or \"then\""

            it "if 0 then escape 0 else escape 1 end" $
                parse stmt_if "if 0 then escape 0 else escape 1 end"
                `shouldBe` Right (If (Const 0) (Escape Nothing (Just (Const 0))) (Escape Nothing (Just (Const 1))))
            it "if 1 then escape 1 end" $
                parse stmt_if "if 1 then escape 1 end"
                `shouldBe` Right (If (Const 1) (Escape Nothing (Just (Const 1))) Nop)
            it "if then escape 1 end" $
                parse stmt_if "if then escape 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else escape 1 end ; end"
                `shouldBe` Right (If (Const 1) (If (Const 0) Nop (Escape Nothing (Just (Const 1)))) Nop)
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else escape 1 end"
                `shouldBe` Right (If (Const 0) (If (Const 0) Nop Nop) (Escape Nothing (Just (Const 1))))

        describe "stmt:" $ do
            it "var int x; escape 1" $
                parse stmt "var int x ;escape 1"
                `shouldBe` Right (Seq (Var "x" Nothing Nothing) (Escape Nothing (Just (Const 1))))

            it "var int x; x<-1; escape x" $
                parse stmt "var int x ; x <- 1 ; escape x"
                `shouldBe` Right (Seq (Var "x" Nothing Nothing) (Seq (Write "x" (Const 1)) (Escape Nothing (Just (Read "x")))))

            it "do ... end" $
                parse stmt "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end"
                `shouldBe` Right (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope (Scope Nop))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

    where
        parse :: Parser a -> String -> Either String a
        parse rule input =
            let v = parseWithEof rule input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
                
