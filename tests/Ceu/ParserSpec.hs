module Test.ParserSpec (main, spec) where

import Test.Hspec

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

    describe "tokens" $ do
        describe "tk_minus" $ do
            it "-" $
                parse tk_minus "- "
                `shouldBe` Right ()
        describe "tk_num" $ do
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
        describe "tk_var" $ do
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
                `shouldBe` Left "TODO: id cannot be a keyword"
        describe "tk_int" $ do
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
                `shouldBe` Left "TODO: id cannot be a keyword"

    describe "expr" $ do
        describe "const" $ do
            it "0" $
                parse expr_const "0"
                `shouldBe` Right (Const 0)
        describe "read" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Read "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Read "aaa")
        describe "umn" $ do
            it "-1" $
                parse expr_umn "-1"
                `shouldBe` Right (Umn (Const 1))
            it "--1" $
                parse expr_umn "--1"
                `shouldBe` Right (Umn (Umn (Const 1)))
        describe "expr" $ do
            it "0" $
                parse expr "0"
                `shouldBe` Right (Const 0)
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Read "aaa")
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Umn (Const 1))

    describe "stmt" $ do
        describe "escape" $ do
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape Nothing (Just (Const 0)))
            it "escape aaa" $
                parse stmt_escape "escape aaa"
                `shouldBe` Right (Escape Nothing (Just (Read "aaa")))

    where
        parse :: Parser a -> String -> Either String a
        parse rule input =
            let v = regularParse rule input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
                
