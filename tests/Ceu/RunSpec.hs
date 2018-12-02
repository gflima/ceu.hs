module Test.RunSpec (main, spec) where

import Test.Hspec

import Text.Parsec.String (Parser)
import FunctionsAndTypesForParsing

import Ceu.Parser.Stmt          (stmt)
import Ceu.Eval                 (Outs)
import Ceu.Grammar.Globals      (Val)
import Ceu.Grammar.Full.Grammar (In)
import Ceu.Grammar.Full.Eval    (evalFullProg)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "void:" $ do
        it "void" $
            run "" []
            `shouldBe` Left "trap: missing `escape` statement\nawait: unreachable statement\n"

    describe "escape:" $ do
        it "escape 1" $
            run "escape 1" []
            `shouldBe` Right (1, [[]])
        it "escape a" $
            run "escape a" []
            `shouldBe` Left "read access to 'a': variable 'a' is not declared\n"
        it "escape" $
            run "escape" []
            `shouldBe` Left "TODO: escape w/o expression"

    describe "exps:" $ do
        it "escape -1" $
            run "escape -1" []
            `shouldBe` Right (-1, [[]])
        it "escape --1" $
            run "escape --1" []
            `shouldBe` Right (1, [[]])
        it "escape - - 1" $
            run "escape - - 1" []
            `shouldBe` Right (1, [[]])
        it "escape ((1))" $
            run "escape ((1))" []
            `shouldBe` Right (1, [[]])
        it "escape ((-9999))" $
            run "escape ((-9999))" []
            `shouldBe` Right (-9999, [[]])
        it "1+2*3" $
            run "escape 1+2*3" []
            `shouldBe` Right (7, [[]])
        it "(1+2)*3" $
            run "escape (1+2)*3" []
            `shouldBe` Right (9, [[]])
        it "1+2-3" $
            run "escape 1+2-3" []
            `shouldBe` Right (0, [[]])
        it "1+2*3/4" $
            run "escape 1+2*3/4" []
            `shouldBe` Right (2, [[]])

    describe "vars:" $ do
        it "var int a,b" $
            run "var int a,b;" []           -- TODO: support a,b,c? (problem w/ assign/finalization)
            `shouldBe` Left "(line 1, column 10):\nunexpected ','\nexpecting digit, letter, \"_\", \"<-\", \"escape\", \"var\", \"await\", \"do\", \"if\", \"par\", \"par/and\", \"par/or\" or end of input"
        it "a <- 1; escape a;" $
            run "a <- 1; escape a" []
            `shouldBe` Left "assignment: variable 'a' is not declared\nread access to 'a': variable 'a' is not declared\n"
        it "var int a <- 1; escape a;" $
            run "var int a <- 1; escape a" []
            `shouldBe` Right (1, [[]])
        it "var int a" $
            run "var int a" []
            `shouldBe` Left "trap: missing `escape` statement\nawait: unreachable statement\n"
        it "var int a <- 1" $
            run "var int a <- 1" []
            `shouldBe` Left "trap: missing `escape` statement\nawait: unreachable statement\n"
        it "var int a ; a <- 1" $
            run "var int a ; a <- 1 ; escape a" []
            `shouldBe` Right (1, [[]])
        it "var int x; x<-1; escape x" $
            run "var int x; x <- 1 ;escape x" []
            `shouldBe` Right (1, [[]])
        it "hide a" $
            run "var int a ; var int a ; escape 0" []
            `shouldBe` Left "declaration: variable 'a' is already declared\n"
        it "do a=1 end ; a=2" $
            run "do var int a <- 1; end var int a <- 2 ; escape a" []
            `shouldBe` Left "TODO: declared but not used"

-------------------------------------------------------------------------------

    describe "awaitext:" $ do
        it "await X ; escape 1" $
            run "await X ; escape 1" []
            `shouldBe` Left "program didn't terminate\n"
        it "await X ; escape 1" $
            run "await X ; escape 1" [("X",Nothing)]
            `shouldBe` Right (1,[[],[]])

-------------------------------------------------------------------------------

    describe "do-end:" $ do
        it "do escape 1 end" $
            run "do escape 1; end" []
            `shouldBe` Right (1, [[]])
        it "do end escape 1" $
            run "do end escape 1;" []
            `shouldBe` Right (1, [[]])
        it "do do do do escape 1 end end end end" $
            run "do do do do escape 1 end end end end" []
            `shouldBe` Right (1, [[]])
        it "do do do do end end end end escape 1" $
            run "do do do; do end ; end end end ;escape 1" []
            `shouldBe` Right (1, [[]])
        it "do ... end" $ do
            run "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end escape 1" []
            `shouldBe` Right (1, [[]])

    describe "if-then-else/if-else" $ do
        it "if 0 then escape 0 else escape 1 end" $
            run "if 0 then escape 0 else escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "if 1 then escape 1 end" $
            run "if 1 then escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "if then (if then else end) end" $
            run "if 1 then ; if 0 then else escape 1 end ; end" []
            `shouldBe` Right (1, [[]])
        it "if then (if then end) else end" $
            run "if 0 then ; if 0 then end ; else escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "if 1 then a=1; a=2; if 1 then escape a end end" $
            run "if 1 then var int a<-1 ; a<-2; if 1 then escape a end end" []
            `shouldBe` Right (2, [[]])
        it "if 0 then . else/if 1 then escape 1 else ." $
            run "if 0 then escape 0 else/if 1 then escape 1 else escape 0 end" []
            `shouldBe` Right (1, [[]])

-------------------------------------------------------------------------------

    describe "par:" $ do
        it "par" $
            run "par do with end" []
            `shouldBe` Left "parallel: terminating trail\ntrap: missing `escape` statement\nawait: unreachable statement\n"
        it "par" $
            run "par do escape 1 with escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "par" $
            run "par do escape 1 with escape 2 with escape 3 end" []
            `shouldBe` Right (1, [[]])

    describe "par/and:" $ do
        it "par/and" $
            run "par/and do with end" []
            `shouldBe` Left "trap: missing `escape` statement\nawait: unreachable statement\n"
        it "par/and; escape 1" $
            run "par/and do with end ; escape 1;" []
            `shouldBe` Right (1, [[]])
        it "par/and ... with ... with escape 3 end" $
            run "par/and do with with escape 3 end" []
            `shouldBe` Left "if: unreachable statement\n"

    describe "par/or:" $ do
        it "par/or" $
            run "par/or do with end" []
            `shouldBe` Left "trap: missing `escape` statement\nawait: unreachable statement\n"
        it "par/or" $
            run "par/or do with end ; escape 1" []
            `shouldBe` Right (1, [[]])
        it "par/or" $
            run "par/or do with escape 2 with escape 3 end ; escape 1" []
            `shouldBe` Left "trap: no trails terminate\n"

    where
        run :: String -> [In] -> Either String (Val,[Outs])
        run input hist =
            let v = parseWithEof stmt input in
                case v of
                    (Right stmt) ->
                        let ret = evalFullProg stmt hist in
                            case ret of
                                (Left errs)           -> Left $ concatMap (\s->s++"\n") errs
                                (Right r@(res,outss)) -> Right r
                    (Left  v') -> Left (show v')
                
