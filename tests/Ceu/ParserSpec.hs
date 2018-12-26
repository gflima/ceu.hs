module Test.ParserSpec (main, spec) where

import Test.Hspec

import qualified Text.Parsec as P (eof, parse)
import Text.Parsec.Prim
import Text.Parsec.String (Parser)

import Ceu.Parser.Token
import Ceu.Parser.Exp
import Ceu.Parser.Stmt
import Ceu.Grammar.Ann.Source
import Ceu.Grammar.Exp          (Exp(..), RawAt(..))
import Ceu.Grammar.Full.Grammar (Stmt(..))

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    --describe "TODO:" $ do

    describe "tokens:" $ do
        describe "comm:" $ do
            it "// xxx " $
                parse comm "// xxx "
                `shouldBe` Right ()
            it "/ xxx " $
                parse comm "/ xxx "
                `shouldBe` Left "(line 1, column 1):\nunexpected \" \"\nexpecting \"//\""
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
        describe "tk_evt:" $ do
            it "''" $
                parse (s>>tk_evt) "\n "
                `shouldBe` Left "(line 2, column 2):\nunexpected end of input"
            it "''" $
                parse tk_evt ""
                `shouldBe` Left "(line 1, column 1):\nunexpected end of input"
            it "id" $
                parse tk_evt "id"
                `shouldBe` Right "id"
            it "1" $
                parse tk_evt "1"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"1\""
            it "var" $
                parse tk_evt "var"
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

        describe "tk_type:" $ do
            it "Int" $
                parse tk_type "Int"
                `shouldBe` Right "Int"
            it "int" $
                parse tk_type "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "I" $
                parse tk_type "I"
                `shouldBe` Left "(line 1, column 2):\nunexpected end of input\nexpecting digit, letter or \"_\""

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

        describe "tk_raw:" $ do
            it "{oi}" $
                parse tk_raw "{oi}"
                `shouldBe` Right [RawAtS "{",RawAtS "oi",RawAtS "}"]
            it "{@oi}" $
                parse tk_raw "{@oi}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read ("",1,3) "oi"),RawAtS "}"]
            it "{@a@b}" $
                parse tk_raw "{@a @b}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read ("",1,3) "a"),RawAtE (Read ("",1,6) "b"),RawAtS "}"]
            it "{@escape}" $
                parse tk_raw "{@escape}"
                `shouldBe` Left "(line 1, column 9):\nunexpected \"}\"\nexpecting digit, letter or \"_\""
            it "{...}" $
                parse tk_raw "{int x = 100}"
                `shouldBe` Right [RawAtS "{",RawAtS "int x = 100",RawAtS "}"]
            it "{o}i} " $
                parse tk_raw "{o}i} "
                `shouldBe` Left "(line 1, column 4):\nunexpected 'i'\nexpecting end of input"
            it "{o}{i} " $
                parse tk_raw "{o}{i} "
                `shouldBe` Left "(line 1, column 4):\nunexpected '{'\nexpecting end of input"
            it "{oi" $
                parse tk_raw "{oi"
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting \"{\", \"@\" or \"}\""
            it "{{oi}}" $
                parse tk_raw "{{oi}}"
                `shouldBe` Right [RawAtS "{",RawAtS "{",RawAtS "oi",RawAtS "}",RawAtS "}"]
            it "{@x+@y}" $
                parse tk_raw "{@x+@y}"
                `shouldBe` Left "(line 1, column 5):\nunexpected \"@\"\nexpecting \"{\", digit, \"-\" or \"(\""
            it "{@x+y}" $
                parse tk_raw "{@x+y}"
                `shouldBe` Right [RawAtS "{",RawAtE (Add ("",1,4) (Read ("",1,3) "x") (Read ("",1,5) "y")),RawAtS "}"]
            it "{@(x)+y}" $
                parse tk_raw "{@(x)+y}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read ("",1,4) "x"),RawAtS "+y",RawAtS "}"]

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_const "0"
                `shouldBe` Right (Const ("",1,1) 0)
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Read ("",1,1) "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Read ("",1,1) "aaa")
        describe "umn:" $ do
            it "-1" $
                parse expr_umn "-1"
                `shouldBe` Right (Umn ("",1,1) (Const ("",1,2) 1))
            it "--1" $
                parse expr_umn "--1"
                `shouldBe` Right (Umn ("",1,1) (Umn ("",1,2) (Const ("",1,3) 1)))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (Const ("",1,2) 1)
            it "((--1))" $
                parse expr_parens "((--1))"
                `shouldBe` Right (Umn ("",1,3) (Umn ("",1,4) (Const ("",1,5) 1)))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr_add_sub "1+1"
                `shouldBe` Right (Add ("",1,2) (Const ("",1,1) 1) (Const ("",1,3) 1))
            it "1+2+3" $
                parse expr_add_sub "1 + 2+3"
                `shouldBe` Right (Add ("",1,6) (Add ("",1,3) (Const ("",1,1) 1) (Const ("",1,5) 2)) (Const ("",1,7) 3))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr_mul_div "1*1"
                `shouldBe` Right (Mul ("",1,2) (Const ("",1,1) 1) (Const ("",1,3) 1))
            it "1*2*3" $
                parse expr_mul_div "1 * 2*3"
                `shouldBe` Right (Mul ("",1,6) (Mul ("",1,3) (Const ("",1,1) 1) (Const ("",1,5) 2)) (Const ("",1,7) 3))
        describe "expr:" $ do
            it "{0}" $
                parse expr "{0}"
                `shouldBe` Right (RawE ("",1,1) [RawAtS "{",RawAtS "0",RawAtS "}"])
            it "0" $
                parse expr "0"
                `shouldBe` Right (Const ("",1,1) 0)
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Read ("",1,1) "aaa")
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Umn ("",1,1) (Const ("",1,3) 1))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (Read ("",1,3) "aaa")
            it "1+2-3" $
                parse expr "1+2-3"
                `shouldBe` Right (Sub ("",1,4) (Add ("",1,2) (Const ("",1,1) 1) (Const ("",1,3) 2)) (Const ("",1,5) 3))
            it "1+2*3" $
                parse expr "1+2*3"
                `shouldBe` Right (Add ("",1,2) (Const ("",1,1) 1) (Mul ("",1,4) (Const ("",1,3) 2) (Const ("",1,5) 3)))
            it "1+2*3/4" $
                parse expr "1+2*3/4"
                `shouldBe` Right (Add ("",1,2) (Const ("",1,1) 1) (Div ("",1,6) (Mul ("",1,4) (Const ("",1,3) 2) (Const ("",1,5) 3)) (Const ("",1,7) 4)))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Mul ("",1,6) (Add ("",1,3) (Const ("",1,2) 1) (Const ("",1,4) 2)) (Const ("",1,7) 3))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right (Nop ("",1,1))

        describe "raw:" $ do
            it "{a}" $
                parse stmt_raw "{a}"
                `shouldBe` Right (RawS ("",1,1) [RawAtS "{",RawAtS "a",RawAtS "}"])
            it "{{a}}" $
                parse stmt_raw "{{a}}"
                `shouldBe` Right (RawS ("",1,1) [RawAtS "{",RawAtS "{",RawAtS "a",RawAtS "}",RawAtS "}"])
            it "{...}" $
                parse stmt_raw "{int x = 100}"
                `shouldBe` Right (RawS ("",1,1) [RawAtS "{",RawAtS "int x = 100",RawAtS "}"])
            it "{...};escape 0" $
                parse stmt "{int x = 100} escape 0"
                `shouldBe` Right (Seq ("",1,1) (RawS ("",1,1) [RawAtS "{",RawAtS "int x = 100",RawAtS "}"]) (Escape ("",1,15) Nothing (Just (Const ("",1,22) 0))))

        describe "escape:" $ do
            it "escape" $
                parse stmt_escape "escape"
                `shouldBe` Right (Escape ("",1,1) Nothing Nothing)
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape ("",1,1) Nothing (Just (Const ("",1,8) 0)))
            it "escape aaa" $
                parse stmt_escape "escape aaa"
                `shouldBe` Right (Escape ("",1,1) Nothing (Just (Read ("",1,8) "aaa")))

        describe "var:" $ do
            it "var x: Int" $
                parse stmt_var "var x: Int;"
                `shouldBe` Right (Seq ("",1,1) (Var ("",1,1) "x" ["Int"] Nothing) (Nop ("",1,1)))
            it "var var x" $
                parse stmt_var "var var x"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "var a: Int <- 1" $
                parse stmt_var "var a : Int <- 1"
                `shouldBe` Right (Seq ("",1,1) (Var ("",1,1) "a" ["Int"] Nothing) (Write ("",1,13) "a" (Const ("",1,16) 1)))
            it "var x : Int <- await X" $
                parse stmt_var "var x : Int <- await X"
                `shouldBe` Right (Seq ("",1,1) (Var ("",1,1) "x" ["Int"] Nothing) (AwaitInp ("",1,16) "X" (Just "x")))

        describe "ext:" $ do
            it "output X: Int" $
                parse stmt_output "output X: Int"
                `shouldBe` Right (Out ("",1,1) "X" True)
            it "output x: Int" $
                parse stmt_output "output x: Int"
                `shouldBe` Left "(line 1, column 8):\nunexpected \"x\""
            it "input X: Int" $
                parse stmt_input "input X: Int"
                `shouldBe` Right (Inp ("",1,1) "X" True)
            it "input x: Int" $
                parse stmt_input "input x: Int"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"x\""

        describe "evt:" $ do
            it "event x: Int" $
                parse stmt_evt "event x: Int;"
                `shouldBe` Right (Evt ("",1,1) "x" True)
            it "event event x" $
                parse stmt_evt "event event x"
                `shouldBe` Left "(line 1, column 12):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "event a: Int <- 1" $
                parse stmt_evt "event a : Int <- 1"
                `shouldBe` Left "(line 1, column 15):\nunexpected '<'\nexpecting end of input"
            it "event x : Int <- await X" $
                parse stmt_evt "event x : Int <- await X"
                `shouldBe` Left "(line 1, column 15):\nunexpected '<'\nexpecting end of input"

        describe "write:" $ do
            it "x <- 1" $
                parse stmt_attr "x <- 1"
                `shouldBe` Right (Write ("",1,3) "x" (Const ("",1,6) 1))
            it "x <- await A" $
                parse stmt_attr "x <- await A"
                `shouldBe` Right (AwaitInp ("",1,6) "A" (Just "x"))
            it "x <- await a" $
                parse stmt_attr "x <- await a"
                `shouldBe` Right (AwaitEvt ("",1,6) "a" (Just "x"))
            it "var <- 1" $
                parse stmt_attr "var <- 1"
                `shouldBe` Left "(line 1, column 4):\nunexpected \" \"\nexpecting digit, letter or \"_\""

-------------------------------------------------------------------------------

        describe "awaitext:" $ do
            it "await X" $
                parse (stmt_awaitext Nothing) "await X"
                `shouldBe` Right (AwaitInp ("",1,1) "X" Nothing)
            it "await x" $
                parse (stmt_awaitext Nothing) "await x"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"x\""

        describe "emitext:" $ do
            it "emit X" $
                parse stmt_emitext "emit X"
                `shouldBe` Right (EmitExt ("",1,1) "X" Nothing)
            it "emit x" $
                parse stmt_emitext "emit x"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"x\""
            it "emit X -> 1" $
                parse stmt_emitext "emit X -> 1"
                `shouldBe` Right (EmitExt ("",1,1) "X" (Just (Const ("",1,11) 1)))

        describe "awaitevt:" $ do
            it "await x" $
                parse (stmt_awaitevt Nothing) "await x"
                `shouldBe` Right (AwaitEvt ("",1,1) "x" Nothing)
            it "await X" $
                parse (stmt_awaitevt Nothing) "await X"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"X\""

        describe "emitevt:" $ do
            it "emit e" $
                parse stmt_emitevt "emit e"
                `shouldBe` Right (EmitEvt ("",1,1) "e" Nothing)
            it "emit x" $
                parse stmt_emitevt "emit X"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"X\""
            it "emit e -> 1" $
                parse stmt_emitevt "emit e -> 1"
                `shouldBe` Right (EmitEvt ("",1,1) "e" (Just (Const ("",1,11) 1)))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do escape 1 end" $
                parse stmt_do "do escape 1 end"
                `shouldBe` Right (Scope ("",1,1) (Escape ("",1,4) Nothing (Just (Const ("",1,11) 1))))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse (tk_key "do" >> (try stmt_escape <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right ()
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (Scope ("",1,1) (Nop ("",1,4)))

        describe "if-then-else/if-else" $ do
            it "if 0 then escape" $
                parse stmt_if "if 0 then escape"
                `shouldBe` Left "(line 1, column 17):\nunexpected end of input\nexpecting letter, \"_\", digit, \"{\", \"-\", \"(\", \"escape\", \"break\", \"var\", \"input\", \"output\", \"event\", \"await\", \"emit\", \"do\", \"if\", \"loop\", \"trap\", \"par\", \"par/and\", \"par/or\", \"else/if\", \"else\" or \"end\""

            it "if 0 then escape 0" $
                parse stmt_if "if 0 then escape 0"
                `shouldBe` Left "(line 1, column 19):\nunexpected end of input\nexpecting digit, \"==\", \"*\", \"/\", \"+\", \"-\", \"{\", \"escape\", \"break\", \"var\", \"input\", \"output\", \"event\", \"await\", \"emit\", \"do\", \"if\", \"loop\", \"trap\", \"par\", \"par/and\", \"par/or\", \"else/if\", \"else\" or \"end\""

            it "if 0 escape 0 end" $
                parse stmt_if "if 0 escape 0 end"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"e\"\nexpecting \"==\", \"*\", \"/\", \"+\", \"-\" or \"then\""

            it "if 0 then escape 0 else escape 1 end" $
                parse stmt_if "if 0 then escape 0 else escape 1 end"
                `shouldBe` Right (If ("",1,1) (Const ("",1,4) 0) (Escape ("",1,11) Nothing (Just (Const ("",1,18) 0))) (Escape ("",1,25) Nothing (Just (Const ("",1,32) 1))))
            it "if 1 then escape 1 end" $
                parse stmt_if "if 1 then escape 1 end"
                `shouldBe` Right (If ("",1,1) (Const ("",1,4) 1) (Escape ("",1,11) Nothing (Just (Const ("",1,18) 1))) (Nop ("",1,20)))
            it "if then escape 1 end" $
                parse stmt_if "if then escape 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else escape 1 end ; end"
                `shouldBe` Right (If ("",1,1) (Const ("",1,4) 1) (If ("",1,13) (Const ("",1,16) 0) (Nop ("",1,23)) (Escape ("",1,28) Nothing (Just (Const ("",1,35) 1)))) (Nop ("",1,43)))
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else escape 1 end"
                `shouldBe` Right (If ("",1,1) (Const ("",1,4) 0) (If ("",1,13) (Const ("",1,16) 0) (Nop ("",1,23)) (Nop ("",1,23))) (Escape ("",1,34) Nothing (Just (Const ("",1,41) 1))))
            it "if 0 then . else/if 1 then escape 1 else ." $
                parse stmt_if "if 0 then escape 0 else/if 1 then escape 1 else escape 0 end"
                `shouldBe` Right (If ("",1,1) (Const ("",1,4) 0) (Escape ("",1,11) Nothing (Just (Const ("",1,18) 0))) (If ("",1,20) (Const ("",1,28) 1) (Escape ("",1,35) Nothing (Just (Const ("",1,42) 1))) (Escape ("",1,49) Nothing (Just (Const ("",1,56) 0)))))

        describe "loop" $ do
            it "loop do end" $
                parse stmt_loop "loop do end"
                `shouldBe` Right (Loop ("",1,1) (Nop ("",1,9)))
            it "loop do v<-1 end" $
                parse stmt_loop "loop do v<-1 end"
                `shouldBe` Right (Loop ("",1,1) (Write ("",1,10) "v" (Const ("",1,12) 1)))
            it "loop do v<-1 ; await FOREVER end" $
                parse stmt_loop "loop do v<-1 ; await FOREVER end"
                `shouldBe` Right (Loop ("",1,1) (Seq ("",1,9) (Write ("",1,10) "v" (Const ("",1,12) 1)) (Halt ("",1,16))))

        describe "trap" $ do
            it "trap do escape end" $
                parse stmt_trap "trap do escape end"
                `shouldBe` Right (Trap ("",1,1) Nothing (Escape ("",1,9) Nothing Nothing))

-------------------------------------------------------------------------------

        describe "par:" $ do
            it "par" $
                parse stmt_par "par do with end"
                `shouldBe` Right (Par ("",1,1) (Nop ("",1,8)) (Nop ("",1,13)))
            it "par" $
                parse stmt_par "par do escape 1 with escape 1 end"
                `shouldBe` Right (Par ("",1,1) (Escape ("",1,8) Nothing (Just (Const ("",1,15) 1))) (Escape ("",1,22) Nothing (Just (Const ("",1,29) 1))))
            it "par" $
                parse stmt_par "par do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Par ("",1,1) (Escape ("",1,8) Nothing (Just (Const ("",1,15) 1))) (Par ("",1,17) (Escape ("",1,22) Nothing (Just (Const ("",1,29) 2))) (Escape ("",1,36) Nothing (Just (Const ("",1,43) 3)))))

        describe "par/and:" $ do
            it "par/and" $
                parse stmt_parand "par/and do with end"
                `shouldBe` Right (And ("",1,1) (Nop ("",1,12)) (Nop ("",1,17)))
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 1 end"
                `shouldBe` Right (And ("",1,1) (Escape ("",1,12) Nothing (Just (Const ("",1,19) 1))) (Escape ("",1,26) Nothing (Just (Const ("",1,33) 1))))
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (And ("",1,1) (Escape ("",1,12) Nothing (Just (Const ("",1,19) 1))) (And ("",1,21) (Escape ("",1,26) Nothing (Just (Const ("",1,33) 2))) (Escape ("",1,40) Nothing (Just (Const ("",1,47) 3)))))

        describe "par/or:" $ do
            it "par/or" $
                parse stmt_paror "par/or do with end"
                `shouldBe` Right (Or ("",1,1) (Nop ("",1,11)) (Nop ("",1,16)))
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 1 end"
                `shouldBe` Right (Or ("",1,1) (Escape ("",1,11) Nothing (Just (Const ("",1,18) 1))) (Escape ("",1,25) Nothing (Just (Const ("",1,32) 1))))
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Or ("",1,1) (Escape ("",1,11) Nothing (Just (Const ("",1,18) 1))) (Or ("",1,20) (Escape ("",1,25) Nothing (Just (Const ("",1,32) 2))) (Escape ("",1,39) Nothing (Just (Const ("",1,46) 3)))))

        describe "seq:" $ do
            it "do end; escape 1" $
                parse (stmt_seq ("",1,1)) "do end escape 1"
                `shouldBe` Right (Seq ("",1,1) (Scope ("",1,1) (Nop ("",1,4))) (Escape ("",1,8) Nothing (Just (Const ("",1,15) 1))))

            it "do end; do end; do end" $
                parse (stmt_seq ("",1,1)) "do end ; do end ; do end"
                `shouldBe` Right (Seq ("",1,1) (Scope ("",1,1) (Nop ("",1,4))) (Seq ("",1,1) (Scope ("",1,10) (Nop ("",1,13))) (Scope ("",1,19) (Nop ("",1,22)))))

            it "input KEY:Int ; var a:Int ; a<-await KEY ; ret<-a" $
                parse (stmt_seq ("",1,1)) "var a:Int ; a<-1"
                `shouldBe` Right (Seq ("",1,1) (Seq ("",1,1) (Var ("",1,1) "a" ["Int"] Nothing) (Nop ("",1,1))) (Write ("",1,14) "a" (Const ("",1,16) 1)))

        describe "stmt:" $ do
            it "var x:Int; escape 1" $
                parse stmt "var x:Int ;escape 1"
                `shouldBe` Right (Seq ("",1,1) (Seq ("",1,1) (Var ("",1,1) "x" ["Int"] Nothing) (Nop ("",1,1))) (Escape ("",1,12) Nothing (Just (Const ("",1,19) 1))))

            it "var x:Int; x<-1; escape x" $
                parse stmt "var x:Int ; x <- 1 ; escape x"
                `shouldBe` Right (Seq ("",1,1) (Seq ("",1,1) (Var ("",1,1) "x" ["Int"] Nothing) (Nop ("",1,1))) (Seq ("",1,1) (Write ("",1,15) "x" (Const ("",1,18) 1)) (Escape ("",1,22) Nothing (Just (Read ("",1,29) "x")))))

            it "do ... end" $
                parse stmt "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end"
                `shouldBe` Right (Scope ("",1,1) (Scope ("",1,4) (Scope ("",1,7) (Scope ("",1,10) (Scope ("",1,13) (Scope ("",1,16) (Scope ("",1,19) (Scope ("",1,22) (Scope ("",1,25) (Scope ("",1,28) (Scope ("",1,31) (Scope ("",1,34) (Scope ("",1,37) (Scope ("",1,40) (Scope ("",1,43) (Scope ("",1,46) (Scope ("",1,49) (Scope ("",1,52) (Scope ("",1,55) (Scope ("",1,58) (Scope ("",1,61) (Scope ("",1,64) (Scope ("",1,67) (Scope ("",1,70) (Scope ("",1,73) (Scope ("",1,76) (Scope ("",1,79) (Scope ("",1,82) (Scope ("",1,85) (Scope ("",1,88) (Scope ("",1,91) (Scope ("",1,94) (Scope ("",1,97) (Scope ("",1,100) (Scope ("",1,103) (Scope ("",1,106) (Scope ("",1,109) (Scope ("",1,112) (Scope ("",1,115) (Scope ("",1,118) (Scope ("",1,121) (Scope ("",1,124) (Scope ("",1,127) (Scope ("",1,130) (Scope ("",1,133) (Scope ("",1,136) (Scope ("",1,139) (Scope ("",1,142) (Scope ("",1,145) (Scope ("",1,148) (Scope ("",1,151) (Scope ("",1,154) (Scope ("",1,157) (Scope ("",1,160) (Scope ("",1,163) (Scope ("",1,166) (Scope ("",1,169) (Scope ("",1,172) (Scope ("",1,175) (Scope ("",1,178) (Scope ("",1,181) (Scope ("",1,184) (Scope ("",1,187) (Scope ("",1,190) (Scope ("",1,193) (Scope ("",1,196) (Scope ("",1,199) (Scope ("",1,202) (Scope ("",1,205) (Scope ("",1,208) (Scope ("",1,211) (Scope ("",1,214) (Scope ("",1,217) (Scope ("",1,220) (Scope ("",1,223) (Scope ("",1,226) (Scope ("",1,229) (Scope ("",1,232) (Scope ("",1,235) (Scope ("",1,238) (Scope ("",1,241) (Scope ("",1,244) (Scope ("",1,247) (Scope ("",1,250) (Scope ("",1,253) (Scope ("",1,256) (Scope ("",1,259) (Scope ("",1,262) (Scope ("",1,265) (Scope ("",1,268) (Scope ("",1,271) (Scope ("",1,274) (Scope ("",1,277) (Scope ("",1,280) (Scope ("",1,283) (Scope ("",1,286) (Scope ("",1,289) (Scope ("",1,292) (Scope ("",1,295) (Scope ("",1,298) (Scope ("",1,301) (Scope ("",1,304) (Scope ("",1,307) (Scope ("",1,310) (Scope ("",1,313) (Scope ("",1,316) (Scope ("",1,319) (Scope ("",1,322) (Scope ("",1,325) (Scope ("",1,328) (Scope ("",1,331) (Scope ("",1,334) (Scope ("",1,337) (Scope ("",1,340) (Scope ("",1,343) (Scope ("",1,346) (Scope ("",1,349) (Scope ("",1,352) (Scope ("",1,355) (Scope ("",1,358) (Scope ("",1,361) (Scope ("",1,364) (Scope ("",1,367) (Scope ("",1,370) (Scope ("",1,373) (Scope ("",1,376) (Scope ("",1,379) (Scope ("",1,382) (Scope ("",1,385) (Scope ("",1,388) (Scope ("",1,391) (Scope ("",1,394) (Scope ("",1,397) (Scope ("",1,400) (Scope ("",1,403) (Scope ("",1,406) (Scope ("",1,409) (Scope ("",1,412) (Scope ("",1,415) (Scope ("",1,418) (Scope ("",1,421) (Scope ("",1,424) (Scope ("",1,427) (Scope ("",1,430) (Scope ("",1,433) (Scope ("",1,436) (Scope ("",1,439) (Scope ("",1,442) (Scope ("",1,445) (Scope ("",1,448) (Scope ("",1,451) (Scope ("",1,454) (Scope ("",1,457) (Scope ("",1,460) (Scope ("",1,463) (Scope ("",1,466) (Scope ("",1,469) (Scope ("",1,472) (Scope ("",1,475) (Scope ("",1,478) (Scope ("",1,481) (Scope ("",1,484) (Scope ("",1,487) (Scope ("",1,490) (Scope ("",1,493) (Scope ("",1,496) (Scope ("",1,499) (Scope ("",1,502) (Scope ("",1,505) (Scope ("",1,508) (Scope ("",1,511) (Scope ("",1,514) (Scope ("",1,517) (Scope ("",1,520) (Scope ("",1,523) (Scope ("",1,526) (Scope ("",1,529) (Scope ("",1,532) (Scope ("",1,535) (Scope ("",1,538) (Scope ("",1,541) (Scope ("",1,544) (Scope ("",1,547) (Scope ("",1,550) (Scope ("",1,553) (Scope ("",1,556) (Scope ("",1,559) (Scope ("",1,562) (Scope ("",1,565) (Scope ("",1,568) (Scope ("",1,571) (Scope ("",1,574) (Scope ("",1,577) (Scope ("",1,580) (Scope ("",1,583) (Scope ("",1,586) (Scope ("",1,589) (Scope ("",1,592) (Scope ("",1,595) (Scope ("",1,598) (Scope ("",1,601) (Scope ("",1,604) (Scope ("",1,607) (Scope ("",1,610) (Scope ("",1,613) (Scope ("",1,616) (Scope ("",1,619) (Scope ("",1,622) (Scope ("",1,625) (Scope ("",1,628) (Scope ("",1,631) (Scope ("",1,634) (Scope ("",1,637) (Scope ("",1,640) (Scope ("",1,643) (Scope ("",1,646) (Scope ("",1,649) (Scope ("",1,652) (Scope ("",1,655) (Scope ("",1,658) (Scope ("",1,661) (Scope ("",1,664) (Scope ("",1,667) (Scope ("",1,670) (Scope ("",1,673) (Scope ("",1,676) (Scope ("",1,679) (Scope ("",1,682) (Scope ("",1,685) (Scope ("",1,688) (Scope ("",1,691) (Scope ("",1,694) (Scope ("",1,697) (Scope ("",1,700) (Scope ("",1,703) (Scope ("",1,706) (Scope ("",1,709) (Scope ("",1,712) (Scope ("",1,715) (Scope ("",1,718) (Scope ("",1,721) (Scope ("",1,724) (Scope ("",1,727) (Scope ("",1,730) (Scope ("",1,733) (Scope ("",1,736) (Scope ("",1,739) (Scope ("",1,742) (Scope ("",1,745) (Scope ("",1,748) (Scope ("",1,751) (Scope ("",1,754) (Scope ("",1,757) (Scope ("",1,760) (Scope ("",1,763) (Scope ("",1,766) (Nop ("",1,769))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

    where
        parse :: Parser a -> String -> Either String a
        parse rule input =
            let v = P.parse (rule <* P.eof) "" input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
