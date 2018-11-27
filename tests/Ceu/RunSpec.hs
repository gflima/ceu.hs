module Test.RunSpec (main, spec) where

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

    describe "escape" $ do
        it "escape 0" $
            run "escape 0"
            `shouldBe` Right (Escape Nothing (Just (Const 0)))

    where
        run :: String -> Either String Stmt
        run input =
            let v = regularParse stmt input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
                
