module Test.RunSpec (main, spec) where

import Test.Hspec

import Text.Parsec (eof, parse)

import Ceu.Parser.Stmt          (stmt)
import Ceu.Eval                 (Outs)
import Ceu.Grammar.Globals      (Source(..), Val)
import Ceu.Grammar.Full.Stmt    (In)
import Ceu.Grammar.Full.Eval    (evalFullProg)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "void:" $ do
        it "void" $
            run "" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n"

    describe "escape:" $ do
        it "escape 1" $
            run "escape 1" []
            `shouldBe` Right (1, [[]])
        it "escape a" $
            run "escape a" []
            `shouldBe` Left "(line 1, column 8):\nvariable 'a' is not declared\n"
        it "escape" $
            run "escape" []
            `shouldBe` Left "(line 1, column 1):\ntypes do not match : Int :> ()\n"

    describe "exps:" $ do
        it "escape -1" $
            run "escape -1" []
            `shouldBe` Right (-1, [[]])
        it "escape - -1" $
            run "escape - -1" []
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
            `shouldBe` Right (9, [[]])
        it "(1+2)*3" $
            run "escape (1+2)*3" []
            `shouldBe` Right (9, [[]])
        it "1+2-3" $
            run "escape 1+2-3" []
            `shouldBe` Right (0, [[]])
        it "1+2*3/4" $
            run "escape 1+2*3/4" []
            `shouldBe` Right (2, [[]])
        it "+ (1 2)" $
            run "escape '+ (1,2)" []
            `shouldBe` Right (3, [[]])

    describe "vars:" $ do
        it "val Int a,b" $
            run "val a,b :Int;" []           -- TODO: support a,b,c? (problem w/ assign/finalization)
            `shouldBe` Left "(line 1, column 6):\nunexpected \",\"\nexpecting digit, letter, \"_\" or \":\""
        it "a <- 1; escape a;" $
            run "set a <- 1; escape a" []
            `shouldBe` Left "(line 1, column 7):\nvariable 'a' is not declared\n(line 1, column 20):\nvariable 'a' is not declared\n"
        it "mut a  : Int <- 1; escape a;" $
            run "mut a  : Int <- 1; escape a" []
            `shouldBe` Right (1, [[]])
        it "val a :Int" $
            run "val a :Int" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n"
        it "mut a :Int <- 1" $
            run "mut a :Int <- 1" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n"
        it "val a :Int ; a <- 1" $
            run "val a :Int ; set a <- 1 ; escape a" []
            `shouldBe` Left "TODO: val cannot be reassigned"
        it "mut a:Int ; a <- 1" $
            run "mut a :Int ; set a <- 1 ; escape a" []
            `shouldBe` Right (1, [[]])
        it "mut x :Int; x<-1; escape x" $
            run "mut x:Int; set x <- 1 ;escape x" []
            `shouldBe` Right (1, [[]])
        it "hide a" $
            run "val a :Int ; val a :Int ; escape 0" []
            `shouldBe` Left "(line 1, column 14):\nvariable 'a' is already declared\n"
        it "do a=1 end ; a=2" $
            run "do val a:Int <- 1; end val a:Int <- 2 ; escape a" []
            `shouldBe` Left "TODO: declared but not used"
        it "mut x:Int <- await X ; escape x" $
            run "input X:Int mut x:Int <- await X ; escape x" [("X",Just 1)]
            `shouldBe` Right (1, [[],[]])
        it "TODO-index-tuples" $
            run "val x:(Int,()) <- (1,()) ; val y:(Int,()) <- x ; escape 1" []
            `shouldBe` Right (1, [[]])
        it "mut x:(Int,Int) <- (1,2) ; escape '+ x | (TODO: no RT support for tuples)" $
            run "mut x:(Int,Int) <- (1,2) ; escape '+ x" []
            `shouldBe` Right (3, [[]])

-------------------------------------------------------------------------------

    describe "awaitext:" $ do
        it "await X ; escape 1" $
            run "input X:Int await X ; escape 1" []
            `shouldBe` Left "program didn't terminate\n"
        it "await X ; escape 1" $
            run "input X:Int await X ; escape 1" [("X",Nothing)]
            `shouldBe` Right (1,[[],[]])
        it "mut x:Int <- await X ; await X ; escape x" $
            run "input X:Int mut x:Int <- await X ; await X ; escape x" [("X",Just 1),("X",Nothing)]
            `shouldBe` Right (1, [[],[],[]])

    describe "emitext:" $ do
        it "emit X" $
            run "output X:() emit X ; escape 1;" []
            `shouldBe` Right (1,[[("X",Nothing)]])
        it "emit X" $
            run "output X :Int emit X ; escape 1;" []
            `shouldBe` Left "(line 1, column 15):\ntypes do not match : Int :> ()\n"
        it "emit x" $
            run "emit x" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n(line 1, column 1):\nevent 'x' is not declared\n"
        it "emit X <- 1" $
            run "output X :Int emit X <- 1 ; escape 2;" []
            `shouldBe` Right (2,[[("X",Just 1)]])
        it "mut x :Int <- await X; emit X <- x ; escape x+1" $
            run "input X :Int mut x :Int <- await X; emit X <- x ; escape x+1" [("X",Just 1)]
            `shouldBe` Left "(line 1, column 37):\noutput 'X' is not declared\n"

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
            `shouldBe` Left "(line 1, column 1):\ntypes do not match : Bool :> Int\n"
        it "if 0==1 then escape 0 else escape 1 end" $
            run "if 0==1 then escape 0 else escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "if 1 then escape 1 end" $
            run "if 1==1 then escape 1 end" []
            --`shouldBe` Right (1, [[]])
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n"
        it "if then (if then else end) end" $
            run "if 1==1 then if 0==1 then await FOREVER else escape 1 end ; end ; await FOREVER; " []
            `shouldBe` Right (1, [[]])
        it "if then (if then end) else end" $
            run "if 0==1 then ; if 0==1 then end ; else escape 1 end ; await FOREVER" []
            `shouldBe` Right (1, [[]])
        it "if 1==1 then a=1; a=2; if 1==1 then escape a end end" $
            run "if 1==1 then val a:Int <-1 ; set a<-2; if 1==1 then escape a end end ; await FOREVER" []
            `shouldBe` Right (2, [[]])
        it "if 0==1 then . else/if 1==1 then escape 1 else ." $
            run "if 0==1 then escape 0 else/if 1==1 then escape 1 else escape 0 end" []
            `shouldBe` Right (1, [[]])

    describe "trap" $ do
        it "trap do escape () end escape 1" $
            run "trap do escape () end escape 1" []
            `shouldBe` Right (1, [[]])

-------------------------------------------------------------------------------

    describe "par:" $ do
        it "par" $
            run "par do with end" []
            `shouldBe` Left "(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nterminating trail\n(line 1, column 1):\nunreachable statement\n"
        it "par" $
            run "par do escape 1 with escape 1 end" []
            `shouldBe` Right (1, [[]])
        it "par" $
            run "par do escape 1 with escape 2 with escape 3 end" []
            `shouldBe` Right (1, [[]])

    describe "par/and:" $ do
        it "par/and" $
            run "par/and do with end" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n"
        it "par/and; escape 1" $
            run "par/and do with end ; escape 1;" []
            `shouldBe` Right (1, [[]])
        it "par/and ... with ... with escape 3 end" $
            run "par/and do with with escape 3 end" []
            --`shouldBe` Right (3, [[]])
            `shouldBe` Left "(line 1, column 12):\ntrail must terminate\n(line 1, column 22):\ntrail must terminate\n"
        it "par/and ... with ... with escape 3 end" $
            run "input X :Int input Y: Int par/and do await X with await Y with escape 3 end" []
            `shouldBe` Left "(line 1, column 64):\ntrail must terminate\n(line 1, column 1):\nterminating `trap` body\n(line 1, column 46):\nunreachable statement\n"

    describe "par/or:" $ do
        it "par/or" $
            run "par/or do with end" []
            `shouldBe` Left "(line 1, column 1):\nterminating `trap` body\n(line 1, column 1):\nmissing `escape` statement\n(line 1, column 1):\nunreachable statement\n"
        it "par/or" $
            run "par/or do with end ; escape 1" []
            `shouldBe` Right (1, [[]])
        it "par/or" $
            run "par/or do with escape 2 with escape 3 end ; escape 1" []
            `shouldBe` Left "(line 1, column 11):\nno trails terminate\n"

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
                
