module Test.RunSpec (main, spec) where

import Test.Hspec

import Text.Parsec.String (Parser)
import FunctionsAndTypesForParsing

import Ceu.Parser.Parser
import Ceu.Eval                 (Outs)
import Ceu.Grammar.Globals      (Val)
import Ceu.Grammar.Full.Grammar (In)
import Ceu.Grammar.Full.Eval    (evalFullProg)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "escape" $ do
        it "escape 1" $
            run "escape 1" []
            `shouldBe` Right (1, [[]])
        it "escape" $
            run "escape" []
            `shouldBe` Right (1, [[]])

    where
        run :: String -> [In] -> Either String (Val,[Outs])
        run input hist =
            let v = regularParse stmt input in
                case v of
                    (Right stmt) ->
                        let ret = evalFullProg stmt hist in
                            case ret of
                                (Left errs)           -> Left $ concatMap (\s->s++"\n") errs
                                (Right r@(res,outss)) -> Right r
                    (Left  v') -> Left (show v')
                
