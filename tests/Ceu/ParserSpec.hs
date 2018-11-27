module Test.ParserSpec (main, spec) where

import Test.Hspec

import Text.Parsec.String (Parser)
import FunctionsAndTypesForParsing

import Ceu.Parser.Parser
import Ceu.Grammar.Globals
import Ceu.Grammar.Full.Grammar

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "num" $ do
        it "''" $
            parse num "\n "
            `shouldBe` Left "(line 2, column 2):\nunexpected end of input\nexpecting digit"
        it "''" $
            parse num ""
            `shouldBe` Left "(line 1, column 1):\nunexpected end of input\nexpecting digit"
        it "1" $
            parse num "1"
            `shouldBe` Right 1
        it "10" $
            parse num "10"
            `shouldBe` Right 10
        it "a" $
            parse num "a"
            `shouldBe` Left "(line 1, column 1):\nunexpected \"a\"\nexpecting digit"

    describe "id_var_evt" $ do
        it "''" $
            parse id_var "\n "
            `shouldBe` Left "(line 2, column 2):\nunexpected end of input"
        it "''" $
            parse id_var ""
            `shouldBe` Left "(line 1, column 1):\nunexpected end of input"
        it "id" $
            parse id_var "id"
            `shouldBe` Right "id"
        it "1" $
            parse id_var "1"
            `shouldBe` Left "(line 1, column 1):\nunexpected \"1\""
        it "var" $
            parse id_var "var"
            `shouldBe` Left "TODO: id cannot be a keyword"

    describe "stmt" $ do
        describe "escape" $ do
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape Nothing (Just (Const 0)))

    where
        parse :: Parser a -> String -> Either String a
        parse rule input =
            let v = regularParse rule input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
                
