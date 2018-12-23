module Test.RunSpec (main, spec) where

import Test.Hspec

import Text.Parsec (eof, parse)

import Ceu.Parser.Stmt          (stmt)
import Ceu.Eval                 (Outs)
import Ceu.Grammar.Ann.Source
import Ceu.Grammar.Globals      (Source(..), Val)
import Ceu.Grammar.Full.Grammar (In)
import Ceu.Grammar.Full.Eval    (evalFullProg)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "void:" $ do
        it "void" $
            run "" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n"

    describe "escape:" $ do
        it "escape 1" $
            run "escape 1" []
            `shouldBe` Right (1, [[]])
        it "escape a" $
            run "escape a" []
            `shouldBe` Left "(line 1, column 8):\nread access to 'a': identifier 'a' is not declared\n"
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
            run "var a,b:int;" []           -- TODO: support a,b,c? (problem w/ assign/finalization)
            `shouldBe` Left "(line 1, column 6):\nunexpected \",\"\nexpecting digit, letter, \"_\" or \":\""
        it "a <- 1; escape a;" $
            run "a <- 1; escape a" []
            `shouldBe` Left "(line 1, column 3):\nassignment: identifier 'a' is not declared\n(line 1, column 16):\nread access to 'a': identifier 'a' is not declared\n"
        it "var a : int <- 1; escape a;" $
            run "var a : int <- 1; escape a" []
            `shouldBe` Right (1, [[]])
        it "var a:int" $
            run "var a:int" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n"
        it "var a:int <- 1" $
            run "var a:int <- 1" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n"
        it "var a:int ; a <- 1" $
            run "var a:int ; a <- 1 ; escape a" []
            `shouldBe` Right (1, [[]])
        it "var x:int; x<-1; escape x" $
            run "var x:int; x <- 1 ;escape x" []
            `shouldBe` Right (1, [[]])
        it "hide a" $
            run "var a:int ; var a:int ; escape 0" []
            `shouldBe` Left "(line 1, column 13):\ndeclaration: identifier 'a' is already declared\n"
        it "do a=1 end ; a=2" $
            run "do var a:int <- 1; end var a:int <- 2 ; escape a" []
            `shouldBe` Left "TODO: declared but not used"
        it "var x:int <- await X ; escape x" $
            run "input X:int var x:int <- await X ; escape x" [("X",Just 1)]
            `shouldBe` Right (1, [[],[]])

-------------------------------------------------------------------------------

    describe "awaitext:" $ do
        it "await X ; escape 1" $
            run "input X:int await X ; escape 1" []
            `shouldBe` Left "program didn't terminate\n"
        it "await X ; escape 1" $
            run "input X:int await X ; escape 1" [("X",Nothing)]
            `shouldBe` Right (1,[[],[]])
        it "var x:int <- await X ; await X ; escape x" $
            run "input X:int var x:int <- await X ; await X ; escape x" [("X",Just 1),("X",Nothing)]
            `shouldBe` Right (1, [[],[],[]])

    describe "emitext:" $ do
        it "emit X" $
            run "output X:int emit X ; escape 1;" []
            `shouldBe` Right (1,[[("X",Nothing)]])
        it "emit x" $
            run "emit x" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n(line 1, column 1):\nemit: identifier 'x' is not declared\n"
        it "emit X -> 1" $
            run "output X:int emit X -> 1 ; escape 2;" []
            `shouldBe` Right (2,[[("X",Just 1)]])
        it "var x:int <- await X; emit X -> x ; escape x+1" $    -- TODO: X in/out
            run "input X:int var x:int <- await X; emit X -> x ; escape x+1" [("X",Just 1)]
            `shouldBe` Right (2,[[],[("X",Just 1)]])

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
            --`shouldBe` Right (1, [[]])
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n"
        it "if then (if then else end) end" $
            run "if 1 then if 0 then await FOREVER else escape 1 end ; end ; await FOREVER; " []
            `shouldBe` Right (1, [[]])
        it "if then (if then end) else end" $
            run "if 0 then ; if 0 then end ; else escape 1 end ; await FOREVER" []
            `shouldBe` Right (1, [[]])
        it "if 1 then a=1; a=2; if 1 then escape a end end" $
            run "if 1 then var a:int <-1 ; a<-2; if 1 then escape a end end ; await FOREVER" []
            `shouldBe` Right (2, [[]])
        it "if 0 then . else/if 1 then escape 1 else ." $
            run "if 0 then escape 0 else/if 1 then escape 1 else escape 0 end" []
            `shouldBe` Right (1, [[]])

    describe "trap" $ do
        it "trap do escape end escape 1" $
            run "trap do escape end escape 1" []
            `shouldBe` Right (1, [[]])

-------------------------------------------------------------------------------

    describe "par:" $ do
        it "par" $
            run "par do with end" []
            `shouldBe` Left "(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nparallel: terminating trail\n(line 1, column 1):\nhalt: unreachable statement\n"
        it "par" $
            run "par do escape 1 with escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "par" $
            run "par do escape 1 with escape 2 with escape 3 end" []
            `shouldBe` Right (1, [[]])

    describe "par/and:" $ do
        it "par/and" $
            run "par/and do with end" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n"
        it "par/and; escape 1" $
            run "par/and do with end ; escape 1;" []
            `shouldBe` Right (1, [[]])
        it "par/and ... with ... with escape 3 end" $
            run "par/and do with with escape 3 end" []
            --`shouldBe` Right (3, [[]])
            `shouldBe` Left "(line 1, column 12):\nsequence: trail must terminate\n(line 1, column 22):\nsequence: trail must terminate\n"
        it "par/and ... with ... with escape 3 end" $
            run "input X:int input Y:int par/and do await X with await Y with escape 3 end" []
            `shouldBe` Left "(line 1, column 62):\nsequence: trail must terminate\n(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 44):\nif: unreachable statement\n"

    describe "par/or:" $ do
        it "par/or" $
            run "par/or do with end" []
            `shouldBe` Left "(line 1, column 1):\ntrap: terminating `trap` body\n(line 1, column 1):\ntrap: missing `escape` statement\n(line 1, column 1):\nhalt: unreachable statement\n"
        it "par/or" $
            run "par/or do with end ; escape 1" []
            `shouldBe` Right (1, [[]])
        it "par/or" $
            run "par/or do with escape 2 with escape 3 end ; escape 1" []
            `shouldBe` Left "(line 1, column 11):\ntrap: no trails terminate\n"

    where
        run :: String -> [In] -> Either String (Val,[Outs])
        run input hist =
            let v = parse (stmt <* eof) "" input in
                case v of
                    (Right p) ->
                        let ret = evalFullProg p hist in
                            case ret of
                                (Left errs)           -> Left $ concatMap (\s->s++"\n") errs
                                (Right r@(res,outss)) -> Right r
                    (Left  v') -> Left (show v')
                
