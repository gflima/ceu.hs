module Test.ParserSpec (main, spec) where

import Test.Hspec

import qualified Text.Parsec as P (eof, parse)
import Text.Parsec.Prim
import Text.Parsec.String (Parser)

import Ceu.Parser.Token
import Ceu.Parser.Type
import Ceu.Parser.Exp
import Ceu.Parser.Stmt
--import Ceu.Grammar.Ann
import Ceu.Grammar.Globals      (Loc(..))
import Ceu.Grammar.Type         (Type(..))
import Ceu.Grammar.Ann          (annz,source,type_)
import Ceu.Grammar.Exp          (Exp(..), RawAt(..))
import Ceu.Grammar.Full.Stmt    (Stmt(..))

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    --describe "TODO:" $ do
        --parse stmt "mut x::Int; val yyy::(Int,Int) : (3,55); ((_,x),_)<:(yyy,1); escape x"

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

        describe "tk_op:" $ do
            it "$$" $
                parse tk_op "$$"
                `shouldBe` Right "($$)"
            it "($$)" $
                parse tk_op "($$)"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"(\""

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
            it "mut" $
                parse tk_var "mut"
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting digit, letter or \"_\""
            it "var" $
                parse tk_var "var"
                `shouldBe` Right "var"
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
            it "event" $
                parse tk_evt "event"
                `shouldBe` Left "(line 1, column 6):\nunexpected end of input\nexpecting digit, letter or \"_\""
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
            it "input" $
                parse tk_ext "input"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
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
                `shouldBe` Right "do"
            it "end" $
                parse (tk_key "end") "end"
                `shouldBe` Right "end"
            it "escape" $
                parse (tk_key "escape") "escape\n"
                `shouldBe` Right "escape"
            it "par/or" $
                parse (tk_key "par/or") "par/or\n"
                `shouldBe` Right "par/or"

        describe "tk_raw:" $ do
            it "{oi}" $
                parse tk_raw "{oi}"
                `shouldBe` Right [RawAtS "{",RawAtS "oi",RawAtS "}"]
            it "{`oi`}" $
                parse tk_raw "{`oi`}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read annz{source=("",1,3)} "oi"),RawAtS "}"]
            it "{`a` `b`}" $
                parse tk_raw "{`a` `b`}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read annz{source=("",1,3)} "a"),RawAtS " ",RawAtE (Read annz{source=("",1,7)} "b"),RawAtS "}"]
            it "{`escape`}" $
                parse tk_raw "{`escape`}"
                `shouldBe` Left "(line 1, column 9):\nunexpected \"`\"\nexpecting digit, letter or \"_\""
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
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting \"{\", \"`\" or \"}\""
            it "{{oi}}" $
                parse tk_raw "{{oi}}"
                `shouldBe` Right [RawAtS "{",RawAtS "{",RawAtS "oi",RawAtS "}",RawAtS "}"]
            it "{`x`+`y`}" $
                parse tk_raw "{`x`+`y`}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read annz{source=("",1,3)} "x"),RawAtS "+",RawAtE (Read annz{source=("",1,7)} "y"),RawAtS "}"]
            it "{`x+y`}" $
                parse tk_raw "{`x+y`}"
                `shouldBe` Right [RawAtS "{",RawAtE (Call annz{source=("",1,4)} "(+)" (Tuple annz{source=("",1,4)} [(Read annz{source=("",1,3)} "x"),(Read annz{source=("",1,5)} "y")])),RawAtS "}"]
            it "{`(x)`+y}" $
                parse tk_raw "{`(x)`+y}"
                `shouldBe` Right [RawAtS "{",RawAtE (Read annz{source=("",1,4)} "x"),RawAtS "+y",RawAtS "}"]

    describe "type:" $ do
        describe "type0" $ do
            it "()" $
                parse type_0 "()"
                `shouldBe` Right Type0
            it "( )" $
                parse type_0 "( )"
                `shouldBe` Right Type0
            it "(())" $
                parse type_0 "(())"
                `shouldBe` Left "(line 1, column 2):\nunexpected \"(\"\nexpecting \")\""
        describe "type1" $ do
            it "Int" $
                parse type_1 "Int"
                `shouldBe` Right (Type1 ["Int"])
            it "III" $
                parse type_1 "III"
                `shouldBe` Left "(line 1, column 4):\nunexpected end of input\nexpecting digit, letter or \"_\""
            it "int" $
                parse type_1 "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
        describe "typeN" $ do
            it "()" $
                parse type_N "()"
                `shouldBe` Left "(line 1, column 2):\nunexpected \")\"\nexpecting \"(\""
            it "(Int)" $
                parse type_N "(Int)"
                `shouldBe` Left "(line 1, column 5):\nunexpected \")\"\nexpecting digit, letter, \"_\" or \",\""
            it "(Int,Int)" $
                parse type_N "(Int,Int)"
                `shouldBe` Right (TypeN [Type1 ["Int"], Type1 ["Int"]])
            it "(Int,())" $
                parse type_N "(Int,())"
                `shouldBe` Right (TypeN [Type1 ["Int"], Type0])

        describe "typeF" $ do
            it "(Int -> Int)" $
                parse type_F "(Int -> Int)"
                `shouldBe` Right (TypeF (Type1 ["Int"]) (Type1 ["Int"]))
            it "(a -> Int)" $
                parse type_F "(a -> Int)"
                `shouldBe` Right (TypeF (TypeV "a") (Type1 ["Int"]))
            it "a -> Int" $
                parse type_F "a -> Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"a\"\nexpecting \"(\""

        describe "typeV" $ do
            it "Int" $
                parse type_V "Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"I\""
            it "a" $
                parse type_V "a"
                `shouldBe` Right (TypeV "a")

        describe "pType" $ do
            it "()" $
                parse pType "()"
                `shouldBe` Right Type0
            it "Int" $
                parse pType "Int"
                `shouldBe` Right (Type1 ["Int"])
            it "(Int, ((),()))" $
                parse pType "(Int, ((),()))"
                `shouldBe` Right (TypeN [Type1 ["Int"], TypeN [Type0,Type0]])

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_const "0"
                `shouldBe` Right (Const annz{source=("",1,1)} 0)
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Read annz{source=("",1,1)} "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Read annz{source=("",1,1)} "aaa")
        describe "umn:" $ do
            it "`-1" $
                parse expr_call_pre "-1"
                `shouldBe` Right (Call annz{source=("",1,1)} "negate" (Const annz{source=("",1,2)} 1))
            it "'--1" $
                parse expr_call_pre "'--1"
                `shouldBe` Right (Call annz{source=("",1,1)} "(--)" (Const annz{source=("",1,4)} 1))
            it "--1" $
                parse expr_call_pre "--1"
                `shouldBe` Right (Call (annz{source = ("",1,1)}) "negate" (Call (annz{source = ("",1,2)}) "negate" (Const (annz{source = ("",1,3)}) 1)))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (Const annz{source=("",1,2)} 1)
            it "((--1))" $
                parse expr_parens "((--1))"
                `shouldBe` Right (Call (annz{source = ("",1,3)}) "negate" (Call (annz{source = ("",1,4)}) "negate" (Const (annz{source = ("",1,5)}) 1)))
            it "((- -1))" $
                parse expr_parens "((- -1))"
                `shouldBe` Right (Call annz{source=("",1,3)} "negate" (Call annz{source=("",1,5)} "negate" (Const annz{source=("",1,6)} 1)))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr_call_mid "1+1"
                `shouldBe` Right (Call annz{source=("",1,2)} "(+)" (Tuple annz{source=("",1,2)} [(Const annz{source=("",1,1)} 1),(Const annz{source=("",1,3)} 1)]))
            it "1+2+3" $
                parse expr_call_mid "1 + 2+3"
                `shouldBe` Right (Call annz{source=("",1,6)} "(+)" (Tuple annz{source=("",1,6)} [(Call annz{source=("",1,3)} "(+)" (Tuple annz{source=("",1,3)} [(Const annz{source=("",1,1)} 1),(Const annz{source=("",1,5)} 2)])),(Const annz{source=("",1,7)} 3)]))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr_call_mid "1*1"
                `shouldBe` Right (Call annz{source=("",1,2)} "(*)" (Tuple annz{source=("",1,2)} [(Const annz{source=("",1,1)} 1),(Const annz{source=("",1,3)} 1)]))
            it "1*2*3" $
                parse expr_call_mid "1 * 2*3"
                `shouldBe` Right (Call annz{source=("",1,6)} "(*)" (Tuple annz{source=("",1,6)} [(Call annz{source=("",1,3)} "(*)" (Tuple annz{source=("",1,3)} [(Const annz{source=("",1,1)} 1),(Const annz{source=("",1,5)} 2)])),(Const annz{source=("",1,7)} 3)]))

        describe "call:" $ do
            it "f 1" $
                parse expr_call_pre "f 1"
                `shouldBe` Right (Call annz{source=("",1,1)} "f" (Const annz{source=("",1,3)} 1))
            it "f 1" $
                parse expr_call_mid "f 1"
                `shouldBe` Right (Call annz{source=("",1,1)} "f" (Const annz{source=("",1,3)} 1))

        describe "tuple:" $ do
            it "(3,55,)" $ do
                parse expr_tuple "(3,55,)"
                `shouldBe` Right (Tuple annz{source=("",1,1)} [Const annz{source=("",1,2)} 3, Const annz{source=("",1,4)} 55])

        describe "expr:" $ do
            it "{0}" $
                parse expr "{0}"
                `shouldBe` Right (RawE annz{source=("",1,1)} [RawAtS "{",RawAtS "0",RawAtS "}"])
            it "0" $
                parse expr "0"
                `shouldBe` Right (Const annz{source=("",1,1)} 0)
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Read annz{source=("",1,1)} "aaa")
            it "'$1" $
                parse expr "'$1"
                `shouldBe` Right (Call annz{source=("",1,1)} "($)" (Const annz{source=("",1,3)} 1))
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Call annz{source=("",1,1)} "negate" (Const annz{source=("",1,3)} 1))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (Read annz{source=("",1,3)} "aaa")
            it "1+2-3" $
                parse expr "1+2-3"
                `shouldBe` Right (Call annz{source=("",1,4)} "(-)" (Tuple annz{source=("",1,4)} [(Call annz{source=("",1,2)} "(+)" (Tuple annz{source=("",1,2)} [(Const annz{source=("",1,1)} 1),(Const annz{source=("",1,3)} 2)])),(Const annz{source=("",1,5)} 3)]))
            it "1+2*3" $
                parse expr "1+2*3"
                `shouldBe` Right (Call annz{source=("",1,4)} "(*)" (Tuple annz{source=("",1,4)} [Call annz{source=("",1,2)} "(+)" (Tuple annz{source=("",1,2)} [Const annz{source=("",1,1)} 1,Const annz{source=("",1,3)} 2]),Const annz{source=("",1,5)} 3]))
            it "1+2*3/4" $
                parse expr "1+2*3/4"
                `shouldBe` Right (Call annz{source=("",1,6)} "(/)" (Tuple annz{source=("",1,6)} [Call annz{source=("",1,4)} "(*)" (Tuple annz{source=("",1,4)} [Call annz{source=("",1,2)} "(+)" (Tuple annz{source=("",1,2)} [Const annz{source=("",1,1)} 1,Const annz{source=("",1,3)} 2]),Const annz{source=("",1,5)} 3]),Const annz{source=("",1,7)} 4]))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Call annz{source=("",1,6)} "(*)" (Tuple annz{source=("",1,6)} [(Call annz{source=("",1,3)} "(+)" (Tuple annz{source=("",1,3)} [(Const annz{source=("",1,2)} 1),(Const annz{source=("",1,4)} 2)])),(Const annz{source=("",1,7)} 3)]))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right (Nop annz{source=("",1,1)})

        describe "raw:" $ do
            it "{a}" $
                parse stmt_raw "{a}"
                `shouldBe` Right (RawS annz{source=("",1,1)} [RawAtS "{",RawAtS "a",RawAtS "}"])
            it "{{a}}" $
                parse stmt_raw "{{a}}"
                `shouldBe` Right (RawS annz{source=("",1,1)} [RawAtS "{",RawAtS "{",RawAtS "a",RawAtS "}",RawAtS "}"])
            it "{...}" $
                parse stmt_raw "{int x = 100}"
                `shouldBe` Right (RawS annz{source=("",1,1)} [RawAtS "{",RawAtS "int x = 100",RawAtS "}"])
            it "{...};escape 0" $
                parse stmt "{int x = 100} escape 0"
                `shouldBe` Right (Seq annz{source=("",1,1)} (RawS annz{source=("",1,1)} [RawAtS "{",RawAtS "int x = 100",RawAtS "}"]) (Escape annz{source=("",1,15)} Nothing (Const annz{source=("",1,22)} 0)))

        describe "escape:" $ do
            it "escape" $
                parse stmt_escape "escape"
                `shouldBe` Right (Escape annz{source=("",1,1)} Nothing (Unit annz{source=("",1,1)}))
            it "escape ()" $
                parse stmt_escape "escape ()"
                `shouldBe` Right (Escape annz{source=("",1,1)} Nothing (Unit annz{source=("",1,8)}))
            it "escape/a ()" $
                parse stmt_escape "escape/a ()"
                `shouldBe` Right (Escape annz{source=("",1,1)} (Just "a") (Unit annz{source=("",1,10)}))
            it "escape 0" $
                parse stmt_escape "escape 0"
                `shouldBe` Right (Escape annz{source=("",1,1)} Nothing (Const annz{source=("",1,8)} 0))
            it "escape aaa" $
                parse stmt_escape "escape aaa"
                `shouldBe` Right (Escape annz{source=("",1,1)} Nothing (Read annz{source=("",1,8)} "aaa"))

        describe "var:" $ do
            it "val x:: Int" $
                parse stmt_var "val x:: Int;"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)})))
            it "mut var x" $
                parse stmt_var "mut var x"
                `shouldBe` Left "(line 1, column 9):\nunexpected \"x\"\nexpecting \"::\""
            it "val a:: Int : 1" $
                parse stmt_var "val a :: Int : 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Write (annz{source = ("",1,14)}) (LVar "a") (Const (annz{source = ("",1,16)}) 1)))
            it "mut x :: Int : await X" $
                parse stmt_var "mut x :: Int : await X"
                `shouldBe` Left "(line 1, column 14):\nunexpected ':'\nexpecting \"<:\" or end of input"
            it "mut x :: Int : await X" $
                parse stmt_var "mut x :: Int <: await X"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (AwaitInp (annz{source = ("",1,17)}) "X" (Just (LVar "x"))))
            it "val x::() : ()" $
                parse stmt_var "val x::() : ()"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" Type0 Nothing) (Nop (annz{source = ("",0,0)}))) (Write (annz{source = ("",1,11)}) (LVar "x") (Unit (annz{source = ("",1,13)}))))
            it "mut x::(Int,()) : (1 ())" $
                parse stmt_var "mut x::(Int,()) <: (1,())"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TypeN [Type1 ["Int"],Type0]) Nothing) (Nop (annz{source = ("",0,0)}))) (Write (annz{source = ("",1,17)}) (LVar "x") (Tuple (annz{source = ("",1,20)}) [Const (annz{source = ("",1,21)}) 1,Unit (annz{source = ("",1,23)})])))

        describe "var-tuples:" $ do
            it "((_,x,),_)" $ do
                parse loc_ "((_,x,),_)"
                `shouldBe` Right (LTuple [LTuple [LAny,LVar "x"],LAny])
            it "val (x,y) :: (Int,Int) : (1, 2); escape x+y" $
                parse stmt_var "val (x,y) :: (Int,Int) : (1, 2)"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)})))) (Write (annz{source = ("",1,24)}) (LTuple [LVar "x",LVar "y"]) (Tuple (annz{source = ("",1,26)}) [Const (annz{source = ("",1,27)}) 1,Const (annz{source = ("",1,30)}) 2])))
            it "mut (x,(y,_))::(Int,(Int,Int)) <: (1, (2,3)); escape x+y" $
                parse stmt "mut (x,(y,_))::(Int, (Int,Int)) <: (1, (2,3)); escape x+y"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)})))) (Write (annz{source = ("",1,33)}) (LTuple [LVar "x",LTuple [LVar "y",LAny]]) (Tuple (annz{source = ("",1,36)}) [Const (annz{source = ("",1,37)}) 1,Tuple (annz{source = ("",1,40)}) [Const (annz{source = ("",1,41)}) 2,Const (annz{source = ("",1,43)}) 3]]))) (Escape (annz{source = ("",1,48)}) Nothing (Call (annz{source = ("",1,56)}) "(+)" (Tuple (annz{source = ("",1,56)}) [Read (annz{source = ("",1,55)}) "x",Read (annz{source = ("",1,57)}) "y"]))))
            it "val (_,_)::(Int,Int,Int)" $
                parse stmt "val (_,_)::(Int,Int,Int)"
                `shouldBe` Left "(line 1, column 25):\nunexpected end of input\nexpecting \":\"\narity mismatch"
            it "val (_,_,_)::(Int,Int)" $
                parse stmt "val (_,_,_)::(Int,Int)"
                `shouldBe` Left "(line 1, column 23):\nunexpected end of input\nexpecting \":\"\narity mismatch"
            it "val (_,_))::Int" $
                parse stmt "val (_,_)::Int"
                `shouldBe` Left "(line 1, column 15):\nunexpected end of input\nexpecting digit, letter, \"_\" or \":\"\narity mismatch"

        describe "ext:" $ do
            it "output X:: Int" $
                parse stmt_output "output X:: Int"
                `shouldBe` Right (Out annz{source=("",1,1)} "X" (Type1 ["Int"]))
            it "output x:: Int" $
                parse stmt_output "output x:: Int"
                `shouldBe` Left "(line 1, column 8):\nunexpected \"x\""
            it "input X:: Int" $
                parse stmt_input "input X:: Int"
                `shouldBe` Right (Inp annz{source=("",1,1)} "X" (Type1 ["Int"]))
            it "input x:: Int" $
                parse stmt_input "input x:: Int"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"x\""

        describe "evt:" $ do
            it "event x:: Int" $
                parse stmt_evt "event x:: Int;"
                `shouldBe` Right (Evt annz{source=("",1,1)} "x" (Type1 ["Int"]))
            it "event event x" $
                parse stmt_evt "event event x"
                `shouldBe` Left "(line 1, column 12):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "event a:: Int : 1" $
                parse stmt_evt "event a :: Int : 1"
                `shouldBe` Left "(line 1, column 16):\nunexpected ':'\nexpecting end of input"
            it "event x :: Int : await X" $
                parse stmt_evt "event x :: Int : await X"
                `shouldBe` Left "(line 1, column 16):\nunexpected ':'\nexpecting end of input"

        describe "write:" $ do
            it "x <: 1" $
                parse stmt_attr "x <: 1"
                `shouldBe` Right (Write annz{source=("",1,3)} (LVar "x") (Const annz{source=("",1,6)} 1))
            it "x <: await A" $
                parse stmt_attr "x <: await A"
                `shouldBe` Right (AwaitInp annz{source=("",1,6)} "A" (Just $ LVar "x"))
            it "x <: await a" $
                parse stmt_attr "x <: await a"
                `shouldBe` Right (AwaitEvt annz{source=("",1,6)} "a" (Just $ LVar "x"))
            it "var <: 1" $
                parse stmt_attr "var <: 1"
                `shouldBe` Right (Write annz{source=("",1,5)} (LVar "var") (Const annz{source=("",1,8)} 1))

-------------------------------------------------------------------------------

        describe "awaitext:" $ do
            it "await X" $
                parse (stmt_awaitext Nothing) "await X"
                `shouldBe` Right (AwaitInp annz{source=("",1,1)} "X" Nothing)
            it "await x" $
                parse (stmt_awaitext Nothing) "await x"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"x\""

        describe "emitext:" $ do
            it "emit X" $
                parse stmt_emitext "emit X"
                `shouldBe` Right (EmitExt annz{source=("",1,1)} "X" (Unit annz{source=("",1,7)}))
            it "emit x" $
                parse stmt_emitext "emit x"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"x\""
            it "emit X -> 1" $
                parse stmt_emitext "emit X -> 1"
                `shouldBe` Right (EmitExt annz{source=("",1,1)} "X" (Const annz{source=("",1,11)} 1))

        describe "awaitevt:" $ do
            it "await x" $
                parse (stmt_awaitevt Nothing) "await x"
                `shouldBe` Right (AwaitEvt annz{source=("",1,1)} "x" Nothing)
            it "await X" $
                parse (stmt_awaitevt Nothing) "await X"
                `shouldBe` Left "(line 1, column 7):\nunexpected \"X\""

        describe "emitevt:" $ do
            it "emit e" $
                parse stmt_emitevt "emit e"
                `shouldBe` Right (EmitEvt annz{source=("",1,1)} "e" Nothing)
            it "emit x" $
                parse stmt_emitevt "emit X"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"X\""
            it "emit e -> 1" $
                parse stmt_emitevt "emit e -> 1"
                `shouldBe` Right (EmitEvt annz{source=("",1,1)} "e" (Just (Const annz{source=("",1,11)} 1)))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do escape 1 end" $
                parse stmt_do "do escape 1 end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Escape annz{source=("",1,4)} Nothing (Const annz{source=("",1,11)} 1)))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse (tk_key "do" >> (try stmt_escape <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)}))

        describe "if-then-else/if-else" $ do
            it "if 0 then escape ()" $
                parse stmt_if "if 0 then escape ()"
                `shouldBe` Left "(line 1, column 20):\nunexpected end of input\nexpecting \"'\", \"{\", \"escape\", \"break\", \"val\", \"mut\", \"input\", \"output\", \"event\", \"func\", \"_\", \"(\", \"await\", \"emit\", \"do\", \"if\", \"loop\", \"trap\", \"par\", \"par/and\", \"par/or\", \"else/if\", \"else\" or \"end\""

            it "if 0 then escape 0" $
                parse stmt_if "if 0 then escape 0"
                `shouldBe` Left "(line 1, column 19):\nunexpected end of input\nexpecting digit, \"'\", \"{\", \"escape\", \"break\", \"val\", \"mut\", \"input\", \"output\", \"event\", \"func\", \"_\", \"(\", \"await\", \"emit\", \"do\", \"if\", \"loop\", \"trap\", \"par\", \"par/and\", \"par/or\", \"else/if\", \"else\" or \"end\""

            it "if 0 escape 0 end" $
                parse stmt_if "if 0 escape 0 end"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"e\"\nexpecting \"'\" or \"then\""

            it "if 0 then escape 0 else escape 1 end" $
                parse stmt_if "if 0 then escape 0 else escape 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (Const annz{source=("",1,4)} 0) (Escape annz{source=("",1,11)} Nothing (Const annz{source=("",1,18)} 0)) (Escape annz{source=("",1,25)} Nothing (Const annz{source=("",1,32)} 1)))
            it "if 1 then escape 1 end" $
                parse stmt_if "if 1 then escape 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (Const annz{source=("",1,4)} 1) (Escape annz{source=("",1,11)} Nothing (Const annz{source=("",1,18)} 1)) (Nop annz{source=("",1,20)}))
            it "if then escape 1 end" $
                parse stmt_if "if then escape 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected \" \"\nexpecting digit, letter or \"_\""
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else escape 1 end ; end"
                `shouldBe` Right (If annz{source=("",1,1)} (Const annz{source=("",1,4)} 1) (If annz{source=("",1,13)} (Const annz{source=("",1,16)} 0) (Nop annz{source=("",1,23)}) (Escape annz{source=("",1,28)} Nothing (Const annz{source=("",1,35)} 1))) (Nop annz{source=("",1,43)}))
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else escape 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (Const annz{source=("",1,4)} 0) (If annz{source=("",1,13)} (Const annz{source=("",1,16)} 0) (Nop annz{source=("",1,23)}) (Nop annz{source=("",1,23)})) (Escape annz{source=("",1,34)} Nothing (Const annz{source=("",1,41)} 1)))
            it "if 0 then . else/if 1 then escape 1 else ." $
                parse stmt_if "if 0 then escape 0 else/if 1 then escape 1 else escape 0 end"
                `shouldBe` Right (If annz{source=("",1,1)} (Const annz{source=("",1,4)} 0) (Escape annz{source=("",1,11)} Nothing (Const annz{source=("",1,18)} 0)) (If annz{source=("",1,20)} (Const annz{source=("",1,28)} 1) (Escape annz{source=("",1,35)} Nothing (Const annz{source=("",1,42)} 1)) (Escape annz{source=("",1,49)} Nothing (Const annz{source=("",1,56)} 0))))

        describe "loop" $ do
            it "loop do end" $
                parse stmt_loop "loop do end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Nop annz{source=("",1,9)}))
            it "loop do v<:1 end" $
                parse stmt_loop "loop do v<:1 end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Write annz{source=("",1,10)} (LVar "v") (Const annz{source=("",1,12)} 1)))
            it "loop do v<:1 ; await FOREVER end" $
                parse stmt_loop "loop do v<:1 ; await FOREVER end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Seq annz{source=("",1,9)} (Write annz{source=("",1,10)} (LVar "v") (Const annz{source=("",1,12)} 1)) (Halt annz{source=("",1,16)})))

        describe "trap" $ do
            it "trap do escape () end" $
                parse (stmt_trap Nothing) "trap do escape () end"
                `shouldBe` Right (Trap annz{source=("",1,1)} Nothing (Escape annz{source=("",1,9)} Nothing (Unit annz{source=("",1,16)})))
            it "val x::() : trap do escape () end" $
                parse stmt_var "val x::() : trap do escape () end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Seq annz (Var annz{source=("",1,1)} "x" Type0 Nothing) (Nop annz{source=("",0,0)})) (Trap annz{source=("",1,13)} (Just "x") (Escape annz{source=("",1,21)} Nothing (Unit annz{source=("",1,28)}))))
            it "mut x::Int <: trap do escape 1 end" $
                parse stmt_var "mut x::Int <: trap do escape 1 end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Seq annz (Var annz{source=("",1,1)} "x" (Type1 ["Int"]) Nothing) (Nop annz{source=("",0,0)})) (Trap annz{source=("",1,15)} (Just "x") (Escape annz{source=("",1,23)} Nothing (Const annz{source=("",1,30)} 1))))
            it "mut x::(Int,()) <: trap do escape (1,()) end" $
                parse stmt_var "mut x::(Int,()) <: trap do escape (1,()) end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Seq annz{source=("",0,0)} (Var annz{source=("",1,1)} "x" (TypeN [Type1 ["Int"],Type0]) Nothing) (Nop annz{source=("",0,0)})) (Trap annz{source=("",1,20)} (Just "x") (Escape annz{source=("",1,28)} Nothing (Tuple annz{source=("",1,35)} [Const annz{source=("",1,36)} 1,Unit annz{source=("",1,38)}]))))

-------------------------------------------------------------------------------

        describe "func:" $ do
            it "func add" $
                parse stmt_func "func add :: ((Int, Int) -> Int)"
                `shouldBe` Right (Func (annz{source = ("",1,1)}) "add" (TypeF (TypeN [Type1 ["Int"],Type1 ["Int"]]) (Type1 ["Int"])))
            it "func add :: i" $
                parse stmt_func "func add :: (a,_) :: ((Int, Int) -> Int)"
                `shouldBe` Right (Func (annz{source = ("",1,1)}) "add" (TypeF (TypeN [Type1 ["Int"],Type1 ["Int"]]) (Type1 ["Int"])))
            it "func add :: i" $
                parse stmt_func "func add :: (_,_,_) :: ((Int, Int) -> Int)"
                `shouldBe` Left "(line 1, column 43):\nunexpected end of input\nexpecting \"do\"\narity mismatch"
            it "funcI add" $
                parse stmt_func "func add :: ((Int, Int) -> Int) do end"
                `shouldBe` Left "(line 1, column 39):\nunexpected end of input\nexpecting letter, \"_\" or digit\nmissing arguments"
            it "funcI add" $
                parse stmt_func "func add :: (a,_) :: ((Int, Int) -> Int) do end"
                `shouldBe` Right (Seq annz{source = ("",1,1)} (Func annz{source = ("",1,1)} "add" (TypeF (TypeN [Type1 ["Int"],Type1 ["Int"]]) (Type1 ["Int"]))) (FuncI (annz{source = ("",1,1)}) "add" (TypeF (TypeN [Type1 ["Int"],Type1 ["Int"]]) (Type1 ["Int"])) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Seq (annz{source = ("",1,1)}) (Write (annz{source = ("",1,1)}) (LTuple [LVar "a",LAny]) (RawE (annz{type_=TypeT, source = ("",1,1)}) [RawAtS "{_ceu_arg}"])) (Nop (annz{source = ("",1,45)}))))))

        describe "par:" $ do
            it "par" $
                parse stmt_par "par do with end"
                `shouldBe` Right (Par annz{source=("",1,1)} (Nop annz{source=("",1,8)}) (Nop annz{source=("",1,13)}))
            it "par" $
                parse stmt_par "par do escape 1 with escape 1 end"
                `shouldBe` Right (Par annz{source=("",1,1)} (Escape annz{source=("",1,8)} Nothing (Const annz{source=("",1,15)} 1)) (Escape annz{source=("",1,22)} Nothing (Const annz{source=("",1,29)} 1)))
            it "par" $
                parse stmt_par "par do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Par annz{source=("",1,1)} (Escape annz{source=("",1,8)} Nothing (Const annz{source=("",1,15)} 1)) (Par annz{source=("",1,17)} (Escape annz{source=("",1,22)} Nothing (Const annz{source=("",1,29)} 2)) (Escape annz{source=("",1,36)} Nothing (Const annz{source=("",1,43)} 3))))

        describe "par/and:" $ do
            it "par/and" $
                parse stmt_parand "par/and do with end"
                `shouldBe` Right (And annz{source=("",1,1)} (Nop annz{source=("",1,12)}) (Nop annz{source=("",1,17)}))
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 1 end"
                `shouldBe` Right (And annz{source=("",1,1)} (Escape annz{source=("",1,12)} Nothing (Const annz{source=("",1,19)} 1)) (Escape annz{source=("",1,26)} Nothing (Const annz{source=("",1,33)} 1)))
            it "par/and" $
                parse stmt_parand "par/and do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (And annz{source=("",1,1)} (Escape annz{source=("",1,12)} Nothing (Const annz{source=("",1,19)} 1)) (And annz{source=("",1,21)} (Escape annz{source=("",1,26)} Nothing (Const annz{source=("",1,33)} 2)) (Escape annz{source=("",1,40)} Nothing (Const annz{source=("",1,47)} 3))))

        describe "par/or:" $ do
            it "par/or" $
                parse stmt_paror "par/or do with end"
                `shouldBe` Right (Or annz{source=("",1,1)} (Nop annz{source=("",1,11)}) (Nop annz{source=("",1,16)}))
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 1 end"
                `shouldBe` Right (Or annz{source=("",1,1)} (Escape annz{source=("",1,11)} Nothing (Const annz{source=("",1,18)} 1)) (Escape annz{source=("",1,25)} Nothing (Const annz{source=("",1,32)} 1)))
            it "par/or" $
                parse stmt_paror "par/or do escape 1 with escape 2 with escape 3 end"
                `shouldBe` Right (Or annz{source=("",1,1)} (Escape annz{source=("",1,11)} Nothing (Const annz{source=("",1,18)} 1)) (Or annz{source=("",1,20)} (Escape annz{source=("",1,25)} Nothing (Const annz{source=("",1,32)} 2)) (Escape annz{source=("",1,39)} Nothing (Const annz{source=("",1,46)} 3))))

        describe "seq:" $ do
            it "do end; escape 1" $
                parse (stmt_seq ("",1,1)) "do end escape 1"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Escape annz{source=("",1,8)} Nothing (Const annz{source=("",1,15)} 1)))

            it "do end; do end; do end" $
                parse (stmt_seq ("",1,1)) "do end ; do end ; do end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Seq annz{source=("",1,1)} (Scope annz{source=("",1,10)} (Nop annz{source=("",1,13)})) (Scope annz{source=("",1,19)} (Nop annz{source=("",1,22)}))))

            it "input KEY::Int ; mut a::Int ; a<:await KEY ; ret<:a" $
                parse (stmt_seq ("",1,1)) "mut a::Int ; a<:1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Write (annz{source = ("",1,15)}) (LVar "a") (Const (annz{source = ("",1,17)}) 1)))

        describe "stmt:" $ do
            it "val x::Int; escape 1" $
                parse stmt "val x::Int ;escape 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Escape (annz{source = ("",1,13)}) Nothing (Const (annz{source = ("",1,20)}) 1)))

            it "mut x::Int; x<:1; escape x" $
                parse stmt "mut x::Int ; x <: 1 ; escape x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type1 ["Int"]) Nothing) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Seq (annz{source = ("",1,1)}) (Write (annz{source = ("",1,16)}) (LVar "x") (Const (annz{source = ("",1,19)}) 1)) (Escape (annz{source = ("",1,23)}) Nothing (Read (annz{source = ("",1,30)}) "x"))))

            it "val x::(Int,Int,):(1,2) ; escape +x" $
                parse stmt "val x::(Int,Int):(1,2) ; escape '+x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TypeN [Type1 ["Int"],Type1 ["Int"]]) Nothing) (Nop (annz{source = ("",0,0)}))) (Write (annz{source = ("",1,17)}) (LVar "x") (Tuple (annz{source = ("",1,18)}) [Const (annz{source = ("",1,19)}) 1,Const (annz{source = ("",1,21)}) 2]))) (Escape (annz{source = ("",1,26)}) Nothing (Call (annz{source = ("",1,33)}) "(+)" (Read (annz{source = ("",1,35)}) "x"))))

            it "do ... end" $
                parse stmt "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Scope annz{source=("",1,4)} (Scope annz{source=("",1,7)} (Scope annz{source=("",1,10)} (Scope annz{source=("",1,13)} (Scope annz{source=("",1,16)} (Scope annz{source=("",1,19)} (Scope annz{source=("",1,22)} (Scope annz{source=("",1,25)} (Scope annz{source=("",1,28)} (Scope annz{source=("",1,31)} (Scope annz{source=("",1,34)} (Scope annz{source=("",1,37)} (Scope annz{source=("",1,40)} (Scope annz{source=("",1,43)} (Scope annz{source=("",1,46)} (Scope annz{source=("",1,49)} (Scope annz{source=("",1,52)} (Scope annz{source=("",1,55)} (Scope annz{source=("",1,58)} (Scope annz{source=("",1,61)} (Scope annz{source=("",1,64)} (Scope annz{source=("",1,67)} (Scope annz{source=("",1,70)} (Scope annz{source=("",1,73)} (Scope annz{source=("",1,76)} (Scope annz{source=("",1,79)} (Scope annz{source=("",1,82)} (Scope annz{source=("",1,85)} (Scope annz{source=("",1,88)} (Scope annz{source=("",1,91)} (Scope annz{source=("",1,94)} (Scope annz{source=("",1,97)} (Scope annz{source=("",1,100)} (Scope annz{source=("",1,103)} (Scope annz{source=("",1,106)} (Scope annz{source=("",1,109)} (Scope annz{source=("",1,112)} (Scope annz{source=("",1,115)} (Scope annz{source=("",1,118)} (Scope annz{source=("",1,121)} (Scope annz{source=("",1,124)} (Scope annz{source=("",1,127)} (Scope annz{source=("",1,130)} (Scope annz{source=("",1,133)} (Scope annz{source=("",1,136)} (Scope annz{source=("",1,139)} (Scope annz{source=("",1,142)} (Scope annz{source=("",1,145)} (Scope annz{source=("",1,148)} (Scope annz{source=("",1,151)} (Scope annz{source=("",1,154)} (Scope annz{source=("",1,157)} (Scope annz{source=("",1,160)} (Scope annz{source=("",1,163)} (Scope annz{source=("",1,166)} (Scope annz{source=("",1,169)} (Scope annz{source=("",1,172)} (Scope annz{source=("",1,175)} (Scope annz{source=("",1,178)} (Scope annz{source=("",1,181)} (Scope annz{source=("",1,184)} (Scope annz{source=("",1,187)} (Scope annz{source=("",1,190)} (Scope annz{source=("",1,193)} (Scope annz{source=("",1,196)} (Scope annz{source=("",1,199)} (Scope annz{source=("",1,202)} (Scope annz{source=("",1,205)} (Scope annz{source=("",1,208)} (Scope annz{source=("",1,211)} (Scope annz{source=("",1,214)} (Scope annz{source=("",1,217)} (Scope annz{source=("",1,220)} (Scope annz{source=("",1,223)} (Scope annz{source=("",1,226)} (Scope annz{source=("",1,229)} (Scope annz{source=("",1,232)} (Scope annz{source=("",1,235)} (Scope annz{source=("",1,238)} (Scope annz{source=("",1,241)} (Scope annz{source=("",1,244)} (Scope annz{source=("",1,247)} (Scope annz{source=("",1,250)} (Scope annz{source=("",1,253)} (Scope annz{source=("",1,256)} (Scope annz{source=("",1,259)} (Scope annz{source=("",1,262)} (Scope annz{source=("",1,265)} (Scope annz{source=("",1,268)} (Scope annz{source=("",1,271)} (Scope annz{source=("",1,274)} (Scope annz{source=("",1,277)} (Scope annz{source=("",1,280)} (Scope annz{source=("",1,283)} (Scope annz{source=("",1,286)} (Scope annz{source=("",1,289)} (Scope annz{source=("",1,292)} (Scope annz{source=("",1,295)} (Scope annz{source=("",1,298)} (Scope annz{source=("",1,301)} (Scope annz{source=("",1,304)} (Scope annz{source=("",1,307)} (Scope annz{source=("",1,310)} (Scope annz{source=("",1,313)} (Scope annz{source=("",1,316)} (Scope annz{source=("",1,319)} (Scope annz{source=("",1,322)} (Scope annz{source=("",1,325)} (Scope annz{source=("",1,328)} (Scope annz{source=("",1,331)} (Scope annz{source=("",1,334)} (Scope annz{source=("",1,337)} (Scope annz{source=("",1,340)} (Scope annz{source=("",1,343)} (Scope annz{source=("",1,346)} (Scope annz{source=("",1,349)} (Scope annz{source=("",1,352)} (Scope annz{source=("",1,355)} (Scope annz{source=("",1,358)} (Scope annz{source=("",1,361)} (Scope annz{source=("",1,364)} (Scope annz{source=("",1,367)} (Scope annz{source=("",1,370)} (Scope annz{source=("",1,373)} (Scope annz{source=("",1,376)} (Scope annz{source=("",1,379)} (Scope annz{source=("",1,382)} (Scope annz{source=("",1,385)} (Scope annz{source=("",1,388)} (Scope annz{source=("",1,391)} (Scope annz{source=("",1,394)} (Scope annz{source=("",1,397)} (Scope annz{source=("",1,400)} (Scope annz{source=("",1,403)} (Scope annz{source=("",1,406)} (Scope annz{source=("",1,409)} (Scope annz{source=("",1,412)} (Scope annz{source=("",1,415)} (Scope annz{source=("",1,418)} (Scope annz{source=("",1,421)} (Scope annz{source=("",1,424)} (Scope annz{source=("",1,427)} (Scope annz{source=("",1,430)} (Scope annz{source=("",1,433)} (Scope annz{source=("",1,436)} (Scope annz{source=("",1,439)} (Scope annz{source=("",1,442)} (Scope annz{source=("",1,445)} (Scope annz{source=("",1,448)} (Scope annz{source=("",1,451)} (Scope annz{source=("",1,454)} (Scope annz{source=("",1,457)} (Scope annz{source=("",1,460)} (Scope annz{source=("",1,463)} (Scope annz{source=("",1,466)} (Scope annz{source=("",1,469)} (Scope annz{source=("",1,472)} (Scope annz{source=("",1,475)} (Scope annz{source=("",1,478)} (Scope annz{source=("",1,481)} (Scope annz{source=("",1,484)} (Scope annz{source=("",1,487)} (Scope annz{source=("",1,490)} (Scope annz{source=("",1,493)} (Scope annz{source=("",1,496)} (Scope annz{source=("",1,499)} (Scope annz{source=("",1,502)} (Scope annz{source=("",1,505)} (Scope annz{source=("",1,508)} (Scope annz{source=("",1,511)} (Scope annz{source=("",1,514)} (Scope annz{source=("",1,517)} (Scope annz{source=("",1,520)} (Scope annz{source=("",1,523)} (Scope annz{source=("",1,526)} (Scope annz{source=("",1,529)} (Scope annz{source=("",1,532)} (Scope annz{source=("",1,535)} (Scope annz{source=("",1,538)} (Scope annz{source=("",1,541)} (Scope annz{source=("",1,544)} (Scope annz{source=("",1,547)} (Scope annz{source=("",1,550)} (Scope annz{source=("",1,553)} (Scope annz{source=("",1,556)} (Scope annz{source=("",1,559)} (Scope annz{source=("",1,562)} (Scope annz{source=("",1,565)} (Scope annz{source=("",1,568)} (Scope annz{source=("",1,571)} (Scope annz{source=("",1,574)} (Scope annz{source=("",1,577)} (Scope annz{source=("",1,580)} (Scope annz{source=("",1,583)} (Scope annz{source=("",1,586)} (Scope annz{source=("",1,589)} (Scope annz{source=("",1,592)} (Scope annz{source=("",1,595)} (Scope annz{source=("",1,598)} (Scope annz{source=("",1,601)} (Scope annz{source=("",1,604)} (Scope annz{source=("",1,607)} (Scope annz{source=("",1,610)} (Scope annz{source=("",1,613)} (Scope annz{source=("",1,616)} (Scope annz{source=("",1,619)} (Scope annz{source=("",1,622)} (Scope annz{source=("",1,625)} (Scope annz{source=("",1,628)} (Scope annz{source=("",1,631)} (Scope annz{source=("",1,634)} (Scope annz{source=("",1,637)} (Scope annz{source=("",1,640)} (Scope annz{source=("",1,643)} (Scope annz{source=("",1,646)} (Scope annz{source=("",1,649)} (Scope annz{source=("",1,652)} (Scope annz{source=("",1,655)} (Scope annz{source=("",1,658)} (Scope annz{source=("",1,661)} (Scope annz{source=("",1,664)} (Scope annz{source=("",1,667)} (Scope annz{source=("",1,670)} (Scope annz{source=("",1,673)} (Scope annz{source=("",1,676)} (Scope annz{source=("",1,679)} (Scope annz{source=("",1,682)} (Scope annz{source=("",1,685)} (Scope annz{source=("",1,688)} (Scope annz{source=("",1,691)} (Scope annz{source=("",1,694)} (Scope annz{source=("",1,697)} (Scope annz{source=("",1,700)} (Scope annz{source=("",1,703)} (Scope annz{source=("",1,706)} (Scope annz{source=("",1,709)} (Scope annz{source=("",1,712)} (Scope annz{source=("",1,715)} (Scope annz{source=("",1,718)} (Scope annz{source=("",1,721)} (Scope annz{source=("",1,724)} (Scope annz{source=("",1,727)} (Scope annz{source=("",1,730)} (Scope annz{source=("",1,733)} (Scope annz{source=("",1,736)} (Scope annz{source=("",1,739)} (Scope annz{source=("",1,742)} (Scope annz{source=("",1,745)} (Scope annz{source=("",1,748)} (Scope annz{source=("",1,751)} (Scope annz{source=("",1,754)} (Scope annz{source=("",1,757)} (Scope annz{source=("",1,760)} (Scope annz{source=("",1,763)} (Scope annz{source=("",1,766)} (Nop annz{source=("",1,769)})))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

    where
        parse :: Parser a -> String -> Either String a
        parse rule input =
            let v = P.parse (rule <* P.eof) "" input in
                case v of
                    (Right v') -> Right v'
                    (Left  v') -> Left (show v')
