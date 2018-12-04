module Test.ParserSpec (main, spec) where

import Test.Hspec

import Text.Parsec.Prim
import Text.Parsec.String (Parser)
import FunctionsAndTypesForParsing

import Ceu.Parser.Token
import Ceu.Parser.Exp
import Ceu.Parser.Stmt
import Ceu.Grammar.Exp          (Exp(..), Exp'(..))
import Ceu.Grammar.Full.Grammar (Stmt(..))

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    --describe "TODO:" $ do

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
            it "Id" $
                parse tk_var "Id"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"I\""
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
        describe "tk_ext:" $ do
            it "''" $
                parse (s>>tk_ext) "\n "
                `shouldBe` Left "(line 2, column 2):\nunexpected end of input"
            it "''" $
                parse tk_ext ""
                `shouldBe` Left "(line 1, column 1):\nunexpected end of input"
            it "id" $
                parse tk_ext "id"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "Id" $
                parse tk_ext "Id"
                `shouldBe` Left "(line 1, column 2):\nunexpected 'd'\nexpecting digit, \"_\" or end of input"
            it "1" $
                parse tk_ext "1"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"1\""
            it "var" $
                parse tk_ext "var"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"v\""
            it "ID" $
                parse tk_ext "ID"
                `shouldBe` Right "ID"

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
            it "par/or" $
                parse (tk_key "par/or") "par/or\n"
                `shouldBe` Right ()

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_const "0"
                `shouldBe` Right (Exp (Const 0, ("",1,1)))
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Exp (Read "a", ("",1,1)))
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Exp (Read "aaa", ("",1,1)))
        describe "umn:" $ do
            it "-1" $
                parse expr_umn "-1"
                `shouldBe` Right (Exp (Umn (Exp (Const 1, ("",1,2))), ("",1,1)))
            it "--1" $
                parse expr_umn "--1"
                `shouldBe` Right (Exp (Umn (Exp (Umn (Exp (Const 1, ("",1,3))), ("",1,2))), ("",1,1)))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (Exp (Const 1, ("",1,2)))
            it "((--1))" $
                parse expr_parens "((--1))"
                `shouldBe` Right (Exp (Umn (Exp (Umn (Exp (Const 1, ("",1,5))), ("",1,4))), ("",1,3)))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr_add_sub "1+1"
                `shouldBe` Right (Exp (Add (Exp (Const 1, ("",1,1))) (Exp (Const 1, ("",1,3))), ("",1,2)))
            it "1+2+3" $
                parse expr_add_sub "1 + 2+3"
                `shouldBe` Right (Exp (Add (Exp (Add (Exp (Const 1, ("",1,1))) (Exp (Const 2, ("",1,5))), ("",1,3))) (Exp (Const 3, ("",1,7))), ("",1,6)))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr_mul_div "1*1"
                `shouldBe` Right (Exp (Mul (Exp (Const 1, ("",1,1))) (Exp (Const 1, ("",1,3))), ("",1,2)))
            it "1*2*3" $
                parse expr_mul_div "1 * 2*3"
                `shouldBe` Right (Exp (Mul (Exp (Mul (Exp (Const 1, ("",1,1))) (Exp (Const 2, ("",1,5))), ("",1,3))) (Exp (Const 3, ("",1,7))), ("",1,6)))
        describe "expr:" $ do
            it "0" $
                parse expr "0"
                `shouldBe` Right (Exp (Const 0, ("",1,1)))
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Exp (Read "aaa", ("",1,1)))
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Exp (Umn (Exp (Const 1, ("",1,3))), ("",1,1)))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (Exp (Read "aaa", ("",1,3)))
            it "1+2-3" $
                parse expr "1+2-3"
                `shouldBe` Right (Exp (Sub (Exp (Add (Exp (Const 1, ("",1,1))) (Exp (Const 2, ("",1,3))), ("",1,2))) (Exp (Const 3, ("",1,5))), ("",1,4)))
            it "1+2*3" $
                parse expr "1+2*3"
                `shouldBe` Right (Exp (Add (Exp (Const 1, ("",1,1))) (Exp (Mul (Exp (Const 2, ("",1,3))) (Exp (Const 3, ("",1,5))), ("",1,4))), ("",1,2)))
            it "1+2*3/4" $
                parse expr "1+2*3/4"
                `shouldBe` Right (Exp (Add (Exp (Const 1, ("",1,1))) (Exp (Div (Exp (Mul (Exp (Const 2, ("",1,3))) (Exp (Const 3, ("",1,5))), ("",1,4))) (Exp (Const 4, ("",1,7))), ("",1,6))), ("",1,2)))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Exp (Mul (Exp (Add (Exp (Const 1, ("",1,2))) (Exp (Const 2, ("",1,4))), ("",1,3))) (Exp (Const 3, ("",1,7))), ("",1,6)))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right Nop

        describe "escape:" $ do
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape Nothing (Just (Exp (Const 0, ("",1,8)))))
            it "escape aaa" $
                parse stmt_escape "escape aaa"
                `shouldBe` Right (Escape Nothing (Just (Exp (Read "aaa", ("",1,8)))))

        describe "var:" $ do
            it "var int x" $
                parse stmt_var "var int x;"
                `shouldBe` Right (Seq (Var "x" Nothing) Nop)
            it "var var x" $
                parse stmt_var "var var x"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "var int a <- 1" $
                parse stmt_var "var int a <- 1"
                `shouldBe` Right (Seq (Var "a" Nothing) (Write "a" (Exp (Const 1, ("",1,14)))))
            it "var int x <- await X" $
                parse stmt_var "var int x <- await X"
                `shouldBe` Right (Seq (Var "x" Nothing) (AwaitExt "X" (Just "x")))

        describe "write:" $ do
            it "x <- 1" $
                parse stmt_write "x <- 1"
                `shouldBe` Right (Write "x" (Exp (Const 1, ("",1,6))))
            it "var <- 1" $
                parse stmt_write "var <- 1"
                `shouldBe` Left "(line 1, column 4):\nunexpected \" \"\nexpecting digit, letter or \"_\""

-------------------------------------------------------------------------------

        describe "awaitext:" $ do
            it "await X" $
                parse (stmt_awaitext Nothing) "await X"
                `shouldBe` Right (AwaitExt "X" Nothing)
            it "await x" $
                parse (stmt_awaitext Nothing) "await x"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"x\""

        describe "emitext:" $ do
            it "emit X" $
                parse stmt_emitext "emit X"
                `shouldBe` Right (EmitExt "X" Nothing)
            it "emit x" $
                parse stmt_emitext "emit x"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"x\""
            it "emit X -> 1" $
                parse stmt_emitext "emit X -> 1"
                `shouldBe` Right (EmitExt "X" (Just (Exp (Const 1, ("",1,11)))))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do escape 1 end" $
                parse stmt_do "do escape 1 end"
                `shouldBe` Right (Scope (Escape Nothing (Just (Exp (Const 1, ("",1,11))))))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse (tk_key "do" >> (try stmt_escape <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (Scope Nop)

        describe "if-then-else/if-else" $ do
            it "if 0 then escape 0" $
                parse stmt_if "if 0 then escape"
                `shouldBe` Left "(line 1, column 11):\nunexpected \"s\"\nexpecting \"end\""

            it "if 0 escape 0 end" $
                parse stmt_if "if 0 escape 0 end"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"e\"\nexpecting \"*\", \"/\", \"+\", \"-\" or \"then\""

            it "if 0 then escape 0 else escape 1 end" $
                parse stmt_if "if 0 then escape 0 else escape 1 end"
                `shouldBe` Right (If (Exp (Const 0, ("",1,4))) (Escape Nothing (Just (Exp (Const 0, ("",1,18))))) (Escape Nothing (Just (Exp (Const 1, ("",1,32))))))
            it "if 1 then escape 1 end" $
                parse stmt_if "if 1 then escape 1 end"
                `shouldBe` Right (If (Exp (Const 1, ("",1,4))) (Escape Nothing (Just (Exp (Const 1, ("",1,18))))) Nop)
            it "if then escape 1 end" $
                parse stmt_if "if then escape 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else escape 1 end ; end"
                `shouldBe` Right (If (Exp (Const 1, ("",1,4))) (If (Exp (Const 0, ("",1,16))) Nop (Escape Nothing (Just (Exp (Const 1, ("",1,35)))))) Nop)
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else escape 1 end"
                `shouldBe` Right (If (Exp (Const 0, ("",1,4))) (If (Exp (Const 0, ("",1,16))) Nop Nop) (Escape Nothing (Just (Exp (Const 1, ("",1,41))))))
            it "if 0 then . else/if 1 then escape 1 else ." $
                parse stmt_if "if 0 then escape 0 else/if 1 then escape 1 else escape 0 end"
                `shouldBe` Right (If (Exp (Const 0, ("",1,4))) (Escape Nothing (Just (Exp (Const 0, ("",1,18))))) (If (Exp (Const 1, ("",1,28))) (Escape Nothing (Just (Exp (Const 1, ("",1,42))))) (Escape Nothing (Just (Exp (Const 0, ("",1,56)))))))

-------------------------------------------------------------------------------

        describe "par:" $ do
            it "par" $
                parse stmt_par "par do with end"
                `shouldBe` Right (Par Nop Nop)
            it "par" $
                parse stmt_par "par do escape 1 with escape 1 end"
                `shouldBe` Right (Par (Escape Nothing (Just (Exp (Const 1, ("",1,15))))) (Escape Nothing (Just (Exp (Const 1, ("",1,29))))))
            it "par" $
                parse stmt_par "par do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Par (Escape Nothing (Just (Exp (Const 1, ("",1,15))))) (Par (Escape Nothing (Just (Exp (Const 2, ("",1,29))))) (Escape Nothing (Just (Exp (Const 3, ("",1,43)))))))

        describe "par/and:" $ do
            it "par/and" $
                parse stmt_parand "par/and do with end"
                `shouldBe` Right (And Nop Nop)
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 1 end"
                `shouldBe` Right (And (Escape Nothing (Just (Exp (Const 1, ("",1,19))))) (Escape Nothing (Just (Exp (Const 1, ("",1,33))))))
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (And (Escape Nothing (Just (Exp (Const 1, ("",1,19))))) (And (Escape Nothing (Just (Exp (Const 2, ("",1,33))))) (Escape Nothing (Just (Exp (Const 3, ("",1,47)))))))

        describe "par/or:" $ do
            it "par/or" $
                parse stmt_paror "par/or do with end"
                `shouldBe` Right (Or Nop Nop)
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 1 end"
                `shouldBe` Right (Or (Escape Nothing (Just (Exp (Const 1, ("",1,18))))) (Escape Nothing (Just (Exp (Const 1, ("",1,32))))))
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Or (Escape Nothing (Just (Exp (Const 1, ("",1,18))))) (Or (Escape Nothing (Just (Exp (Const 2, ("",1,32))))) (Escape Nothing (Just (Exp (Const 3, ("",1,46)))))))

        describe "seq:" $ do
            it "do end; escape 1" $
                parse stmt_seq "do end escape 1"
                `shouldBe` Right (Seq (Scope Nop) (Escape Nothing (Just (Exp (Const 1, ("",1,15))))))

        describe "stmt:" $ do
            it "var int x; escape 1" $
                parse stmt "var int x ;escape 1"
                `shouldBe` Right (Seq (Seq (Var "x" Nothing) Nop) (Escape Nothing (Just (Exp (Const 1, ("",1,19))))))

            it "var int x; x<-1; escape x" $
                parse stmt "var int x ; x <- 1 ; escape x"
                `shouldBe` Right (Seq (Seq (Var "x" Nothing) Nop) (Seq (Write "x" (Exp (Const 1, ("",1,18)))) (Escape Nothing (Just (Exp (Read "x", ("",1,29)))))))

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
                
