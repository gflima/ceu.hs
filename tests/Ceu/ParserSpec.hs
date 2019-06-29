{-# LANGUAGE QuasiQuotes #-}

module Ceu.ParserSpec (main, spec) where

import Test.Hspec
import Text.RawString.QQ
import Data.Set as S (fromList)
import Data.Map as M (fromList)

import qualified Text.Parsec as P (eof, parse)
import Text.Parsec.Prim hiding (Error)
import Text.Parsec.String (Parser)

import Ceu.Parser.Token
import Ceu.Parser.Type
--import Ceu.Parser.Exp
import Ceu.Parser.Stmt
--import Ceu.Grammar.Ann
import Ceu.Grammar.Globals
import Ceu.Grammar.Constraints  (cz,cv,cvc)
import Ceu.Grammar.Type         (Type(..))
import Ceu.Grammar.Ann          (annz,source,type_)
import Ceu.Grammar.Full.Full    (Stmt(..), Exp(..), Loc(..))
import Ceu.Grammar.Full.Eval    (prelude, compile')
import qualified Ceu.Grammar.Basic as B

clearStmt :: Stmt -> Stmt
clearStmt (Class _ id  cs ifc)     = Class annz id  cs (clearStmt ifc)
clearStmt (Inst  _ cls tp imp)     = Inst  annz cls tp (clearStmt imp)
clearStmt (Data  _ tp abs)         = Data  annz tp abs
clearStmt (Var   _ var tp)         = Var   annz var tp
clearStmt (FuncS _ var tp p)       = FuncS annz var tp (clearStmt p)
--clearStmt (Match _ l r t f)      = Match annz (clearExp l) (clearExp r) (clearStmt t) (clearStmt f)
clearStmt (Set   _ chk loc exp)    = Set   annz chk loc (clearExp exp)
clearStmt (If    _ exp p1 p2)      = If    annz (clearExp exp) (clearStmt p1) (clearStmt p2)
clearStmt (Seq   _ p1 p2)          = Seq   annz (clearStmt p1) (clearStmt p2)
clearStmt (Loop  _ p)              = Loop  annz (clearStmt p)
clearStmt (Nop   _)                = Nop   annz
clearStmt (Scope  _ p)             = Scope annz (clearStmt p)
clearStmt (Ret   _ exp)            = Ret   annz (clearExp exp)
clearStmt p                        = error $ "clearStmt: unexpected statement: " ++ (show p)

clearExp :: Exp -> Exp
clearExp (Number _ v)     = Number annz v
clearExp (Cons   _ v)     = Cons   annz v
clearExp (Read   _ v)     = Read   annz v
clearExp (Arg    _)       = Arg    annz
clearExp (Unit   _)       = Unit   annz
clearExp (Tuple  _ es)    = Tuple  annz (map clearExp es)
clearExp (Func   _ tp p)  = Func   annz tp (clearStmt p)
clearExp (Call   _ e1 e2) = Call   annz (clearExp e1) (clearExp e2)

fromRight' :: Either a b -> b
fromRight' (Right x) = x

int  = TypeD ["Int"]  [] Type0
bool = TypeD ["Bool"] [] Type0

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

{-
    describe "TODO:" $ do
      it "and" $
        (parse' stmt $
          unlines [
            "func and (x,y) : ((Bool,Bool)->Bool) do",
            "   return Bool.False",
            "end",
            "return Bool.True and Bool.False"
           ])
        `shouldBe` Left "XXX"
-}

    describe "tokens:" $ do
        describe "comm:" $ do
            it "// xxx " $
                parse comm "// xxx "
                `shouldBe` Right ()
            it "/ xxx " $
                parse comm "/ xxx "
                `shouldBe` Left "(line 1, column 1):\nunexpected \" \""

        describe "tk_sym:" $ do
            it "(" $
                parse (tk_sym "(") "( "
                `shouldBe` Right ()
            it ")" $
                parse (tk_sym ")") ") "
                `shouldBe` Right ()
            it "-" $
                parse (tk_sym "-") "- "
                `shouldBe` Right ()

        describe "tk_op:" $ do
            it "$$" $
                parse tk_op "$$"
                `shouldBe` Right "$$"
            it "$$" $
                parse tk_op "($$)"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"(\"\nexpecting operator"
            it "->" $
                parse tk_op "->"
                `shouldBe` Left "(line 1, column 3):\nunexpected arrow\nexpecting operator"

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
                `shouldBe` Left "(line 1, column 4):\nunexpected `var`\nexpecting identifier"

        describe "tk_data:" $ do
            it "Int" $
                parse tk_data "Int"
                `shouldBe` Right "Int"
            it "U8" $
                parse tk_data "U8"
                `shouldBe` Right "U8"
            it "int" $
                parse tk_data "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "I" $
                parse tk_data "I"
                --`shouldBe` Left "(line 1, column 2):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right "I"
            it "III" $
                parse tk_data "III"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right "III"
            it "IEq" $
                parse tk_data "IEq"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right "IEq"

        describe "tk_data_hier:" $ do
            it "Int.X" $
                parse tk_data_hier "Int.X"
                --`shouldBe` Left "(line 1, column 6):\nunexpected end of input\nexpecting data identifier"
                `shouldBe` Right ["Int", "X"]
            it "Bool.True" $
                parse tk_data_hier "Bool.True"
                `shouldBe` Right ["Bool","True"]
            it "U8.IEq" $
                parse tk_data_hier "U8.IEq"
                --`shouldBe` Left "(line 1, column 7):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right ["U8","IEq"]
            it "Int.U8" $
                parse tk_data_hier "Int.U8"
                `shouldBe` Right ["Int", "U8"]
            it "int.X" $
                parse tk_data_hier "int.X"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "I" $
                parse tk_data_hier "I"
                --`shouldBe` Left "(line 1, column 2):\nunexpected end of input\nexpecting data identifier"
                `shouldBe` Right ["I"]
            it "III" $
                parse tk_data_hier "III"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right ["III"]
            it "IEq" $
                parse tk_data_hier "IEq"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right ["IEq"]

        describe "tk_class:" $ do
            it "Int" $
                parse tk_class "Int"
                `shouldBe` Left "(line 1, column 2):\nunexpected \"n\""
            it "U8" $
                parse tk_class "U8"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"U\"\nexpecting \"I\""
            it "int" $
                parse tk_class "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\"\nexpecting \"I\""
            it "I" $
                parse tk_class "I"
                `shouldBe` Left "(line 1, column 2):\nunexpected end of input"
            it "III" $
                parse tk_class "III"
                `shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting constraint identifier"

        describe "tk_key:" $ do
            it "do" $
                parse (tk_key "do") "do "
                `shouldBe` Right "do"
            it "end" $
                parse (tk_key "end") "end"
                `shouldBe` Right "end"
            it "return" $
                parse (tk_key "return") "return\n"
                `shouldBe` Right "return"
            it "ret" $
                parse (tk_key "return") "ret\n"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"\\n\"\nexpecting \"return\""
            it "returns" $
                parse (tk_key "return") "returns\n"
                `shouldBe` Left "(line 1, column 8):\nunexpected 's'"

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
        describe "typeD" $ do
            it "Int" $
                parse type_D "Int"
                `shouldBe` Right (int)
            it "III" $
                parse type_D "III"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right (TypeD ["III"] [] Type0)
            it "int" $
                parse type_D "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "Int of ()" $
                parse type_D "Int of ()"
                `shouldBe` Right (int)
            it "Int of Int of Int" $
                parse type_D "Int of Int of Int"
                `shouldBe` Right (TypeD ["Int"] [TypeD ["Int"] [int] Type0] Type0)
            it "Tree of (Int,Int)" $
                parse type_D "Tree of (Int,Int)"
                `shouldBe` Right (TypeD ["Tree"] [int, int] Type0)
        describe "typeN" $ do
            it "()" $
                parse type_N "()"
                `shouldBe` Left "(line 1, column 2):\nunexpected \")\"\nexpecting type"
            it "(Int)" $
                parse type_N "(Int)"
                `shouldBe` Left "(line 1, column 5):\nunexpected \")\"\nexpecting data identifier, \".\", \"of\" or \",\""
            it "(Int,Int)" $
                parse type_N "(Int,Int)"
                `shouldBe` Right (TypeN [int, int])
            it "(Int,())" $
                parse type_N "(Int,())"
                `shouldBe` Right (TypeN [int, Type0])

        describe "typeF" $ do
            it "(Int -> Int)" $
                parse type_F "(Int -> Int)"
                `shouldBe` Right (TypeF (int) (int))
            it "(a -> Int)" $
                parse type_F "(a -> Int)"
                `shouldBe` Right (TypeF (TypeV "a") (int))
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
                `shouldBe` Right (int)
            it "(Int, ((),()))" $
                parse pType "(Int, ((),()))"
                `shouldBe` Right (TypeN [int, TypeN [Type0,Type0]])

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_number "0"
                `shouldBe` Right (Number annz{source=("",1,1)} 0)
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (Read annz{source=("",1,1)} "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (Read annz{source=("",1,1)} "aaa")
        describe "umn:" $ do
            it "-1" $
                parse expr "-1"
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "negate") (Number annz{source=("",1,2)} 1))
            it "--1" $
                parse expr "--1"
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "--") (Number annz{source=("",1,3)} 1))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (Number annz{source=("",1,2)} 1)
            it "((- +1))" $
                parse expr_parens "((- +1))"
                `shouldBe` Right (Call annz{source=("",1,5)} (Read annz{source=("",1,5)} "+") (Tuple annz{source=("",1,3)} [Read annz{source=("",1,3)} "-",Number annz{source=("",1,6)} 1]))
            it "(- (-1))" $
                parse expr_parens "(- (+1))"
                `shouldBe` Right (Call annz{source=("",1,2)} (Read annz{source=("",1,2)} "negate") (Call annz{source=("",1,5)} (Read annz{source=("",1,5)} "+") (Number annz{source=("",1,6)} 1)))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr "1+1"
                `shouldBe` Right (Call annz{source=("",1,2)} (Read annz{source=("",1,2)} "+") (Tuple annz{source=("",1,1)} [(Number annz{source=("",1,1)} 1),(Number annz{source=("",1,3)} 1)]))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr "1*1"
                `shouldBe` Right (Call annz{source=("",1,2)} (Read annz{source=("",1,2)} "*") (Tuple annz{source=("",1,1)} [(Number annz{source=("",1,1)} 1),(Number annz{source=("",1,3)} 1)]))
            it "(1*2)*3" $
                parse expr "(1 * 2)*3"
                `shouldBe` Right (Call annz{source=("",1,8)} (Read annz{source=("",1,8)} "*") (Tuple annz{source=("",1,4)} [(Call annz{source=("",1,4)} (Read annz{source=("",1,4)} "*") (Tuple annz{source=("",1,2)} [(Number annz{source=("",1,2)} 1),(Number annz{source=("",1,6)} 2)])),(Number annz{source=("",1,9)} 3)]))

        describe "call:" $ do
            it "f 1" $
                parse expr "f 1"
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "f") (Number annz{source=("",1,3)} 1))
            it "f 1" $
                parse expr "f 1"
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "f") (Number annz{source=("",1,3)} 1))

        describe "tuple:" $ do
            it "(3,55,)" $ do
                parse expr_tuple "(3,55,)"
                `shouldBe` Right (Tuple annz{source=("",1,1)} [Number annz{source=("",1,2)} 3, Number annz{source=("",1,4)} 55])

        describe "expr:" $ do
            it "0" $
                parse expr "0"
                `shouldBe` Right (Number annz{source=("",1,1)} 0)
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (Read annz{source=("",1,1)} "aaa")
            it "$1" $
                parse expr "$1"
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "$") (Number annz{source=("",1,2)} 1))
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (Call annz{source=("",1,1)} (Read annz{source=("",1,1)} "negate") (Number annz{source=("",1,3)} 1))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (Read annz{source=("",1,3)} "aaa")
            it "(1+2)-3" $
                parse expr "(1+2)-3"
                `shouldBe` Right (Call annz{source=("",1,6)} (Read annz{source=("",1,6)} "-") (Tuple annz{source=("",1,3)} [(Call annz{source=("",1,3)} (Read annz{source=("",1,3)} "+") (Tuple annz{source=("",1,2)} [(Number annz{source=("",1,2)} 1),(Number annz{source=("",1,4)} 2)])),(Number annz{source=("",1,7)} 3)]))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Call annz{source=("",1,6)} (Read annz{source=("",1,6)} "*") (Tuple annz{source=("",1,3)} [Call annz{source=("",1,3)} (Read annz{source=("",1,3)} "+") (Tuple annz{source=("",1,2)} [Number annz{source=("",1,2)} 1,Number annz{source=("",1,4)} 2]),Number annz{source=("",1,7)} 3]))
            it "((1+2)*3)/4" $
                parse expr "((1+2)*3)/4"
                `shouldBe` Right (Call annz{source=("",1,10)} (Read annz{source=("",1,10)} "/") (Tuple annz{source=("",1,7)} [Call annz{source=("",1,7)} (Read annz{source=("",1,7)} "*") (Tuple annz{source=("",1,4)} [Call annz{source=("",1,4)} (Read annz{source=("",1,4)} "+") (Tuple annz{source=("",1,3)} [Number annz{source=("",1,3)} 1,Number annz{source=("",1,5)} 2]),Number annz{source=("",1,8)} 3]),Number annz{source=("",1,11)} 4]))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (Call annz{source=("",1,6)} (Read annz{source=("",1,6)} "*") (Tuple annz{source=("",1,3)} [(Call annz{source=("",1,3)} (Read annz{source=("",1,3)} "+") (Tuple annz{source=("",1,2)} [(Number annz{source=("",1,2)} 1),(Number annz{source=("",1,4)} 2)])),(Number annz{source=("",1,7)} 3)]))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right (Nop annz{source=("",1,1)})

        describe "var:" $ do
            it "var x: Int" $
                parse stmt_var "var x: Int;"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)})))
            it "var val x" $
                parse stmt_var "var val x"
                `shouldBe` Left "(line 1, column 9):\nunexpected \"x\"\nexpecting \":\""
            it "var a: Int <- 1" $
                parse stmt_var "var a : Int <- 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,13)}) False (LVar "a") (Number (annz{source = ("",1,16)}) 1)))
            it "var x:() <- ()" $
                parse stmt_var "var x:() <- ()"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (Type0,cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,10)}) False (LVar "x") (Unit (annz{source = ("",1,13)}))))
            it "var x:(Int,()) <- (1 ())" $
                parse stmt_var "var x:(Int,()) <- (1,())"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TypeN [int,Type0],cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,16)}) False (LVar "x") (Tuple (annz{source = ("",1,19)}) [Number (annz{source = ("",1,20)}) 1,Unit (annz{source = ("",1,22)})])))

        describe "var-tuples:" $ do
            it "((_,x,),_)" $ do
                parse pLoc "((_,x,),_)"
                `shouldBe` Right (LTuple [LTuple [LAny,LVar "x"],LAny])
            it "var (x,y) : (Int,Int) <- (1, 2); return x+y" $
                parse stmt_var "var (x,y) : (Int,Int) <- (1, 2)"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (int,cz)) (Nop (annz{source = ("",0,0)})))) (Set (annz{source = ("",1,23)}) False (LTuple [LVar "x",LVar "y"]) (Tuple (annz{source = ("",1,26)}) [Number (annz{source = ("",1,27)}) 1,Number (annz{source = ("",1,30)}) 2])))
            it "var (x,(y,_)):(Int,(Int,Int)) <- (1, (2,3)); return x+y" $
                parse stmt "var (x,(y,_)):(Int, (Int,Int)) <- (1, (2,3)); return x+y"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (int,cz)) (Nop (annz{source = ("",0,0)})))) (Set (annz{source = ("",1,32)}) False (LTuple [LVar "x",LTuple [LVar "y",LAny]]) (Tuple (annz{source = ("",1,35)}) [Number (annz{source = ("",1,36)}) 1,Tuple (annz{source = ("",1,39)}) [Number (annz{source = ("",1,40)}) 2,Number (annz{source = ("",1,42)}) 3]]))) (Ret (annz{source = ("",1,47)}) (Call (annz{source = ("",1,55)}) (Read annz{source=("",1,55)} "+") (Tuple (annz{source = ("",1,54)}) [Read (annz{source = ("",1,54)}) "x",Read (annz{source = ("",1,56)}) "y"]))))
            it "var (_,_):(Int,Int,Int)" $
                parse stmt "var (_,_):(Int,Int,Int)"
                `shouldBe` Left "(line 1, column 24):\nunexpected arity mismatch\nexpecting \"where\""
            it "var (_,_,_):(Int,Int)" $
                parse stmt "var (_,_,_):(Int,Int)"
                `shouldBe` Left "(line 1, column 22):\nunexpected arity mismatch\nexpecting \"where\""
            it "var (_,_)):Int" $
                parse stmt "var (_,_):Int"
                `shouldBe` Left "(line 1, column 14):\nunexpected arity mismatch\nexpecting data identifier, \".\", \"of\" or \"where\""

        describe "write:" $ do
            it "x <- 1" $
                parse stmt_attr "set x <- 1"
                `shouldBe` Right (Set annz{source=("",1,7)} False (LVar "x") (Number annz{source=("",1,10)} 1))
            it "val <- 1" $
                parse stmt_attr "set val <- 1"
                `shouldBe` Right (Set annz{source=("",1,9)} False (LVar "val") (Number annz{source=("",1,12)} 1))

        describe "call:" $ do
          it "call 1" $
            parse stmt_call "call 1"
            `shouldBe` Right (CallS annz{source = ("",1,1)} (Number annz{source=("",1,6)} 1))
          it "call print" $
            parse stmt_call "call print 1"
            `shouldBe` Right (CallS (annz {source = ("",1,1)}) (Call (annz {source = ("",1,6)}) (Read (annz {source = ("",1,6)}) "print") (Number (annz {source = ("",1,12)}) 1)))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do return 1 end" $
                parse stmt_do "do return 1 end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Ret annz{source=("",1,4)} (Number annz{source=("",1,11)} 1)))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse (tk_key "do" >> (try stmt_ret <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)}))

        describe "if-then-else/if-else" $ do
            it "if 0 then return ()" $
                parse stmt_match "if 0 then return ()"
                `shouldBe` Left "(line 1, column 20):\nunexpected end of input\nexpecting expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 then return 0" $
                parse stmt_match "if 0 then return 0"
                `shouldBe` Left "(line 1, column 19):\nunexpected end of input\nexpecting digit, expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 return 0 end" $
                parse stmt_match "if 0 return 0 end"
                `shouldBe` Left "(line 1, column 12):\nunexpected `return`\nexpecting expression"

            it "if 0 then return 0 else return 1 end" $
                parse stmt_match "if 0 then return 0 else return 1 end"
                `shouldBe` Right (Match annz{source=("",1,1)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,4)} 0) (Ret annz{source=("",1,11)} (Number annz{source=("",1,18)} 0)) (Ret annz{source=("",1,25)} (Number annz{source=("",1,32)} 1)))
            it "if 1 then return 1 end" $
                parse stmt_match "if 1 then return 1 end"
                `shouldBe` Right (Match annz{source=("",1,1)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,4)} 1) (Ret annz{source=("",1,11)} (Number annz{source=("",1,18)} 1)) (Nop annz{source=("",1,20)}))
            it "if then return 1 end" $
                parse stmt_match "if then return 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected `then`\nexpecting identifier or expression"
            it "if then (if then else end) end" $
                parse stmt_match "if 1 then ; if 0 then else return 1 end ; end"
                `shouldBe` Right (Match annz{source=("",1,1)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,4)} 1) (Match annz{source=("",1,13)} (LExp (Read annz{source=("",1,13)} "_true")) (Number annz{source=("",1,16)} 0) (Nop annz{source=("",1,23)}) (Ret annz{source=("",1,28)} (Number annz{source=("",1,35)} 1))) (Nop annz{source=("",1,43)}))
            it "if then (if then end) else end" $
                parse stmt_match "if 0 then ; if 0 then end ; else return 1 end"
                `shouldBe` Right (Match annz{source=("",1,1)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,4)} 0) (Match annz{source=("",1,13)} (LExp (Read annz{source=("",1,13)} "_true")) (Number annz{source=("",1,16)} 0) (Nop annz{source=("",1,23)}) (Nop annz{source=("",1,23)})) (Ret annz{source=("",1,34)} (Number annz{source=("",1,41)} 1)))
            it "if 0 then . else/if 1 then return 1 else ." $
                parse stmt_match "if 0 then return 0 else/if 1 then return 1 else return 0 end"
                `shouldBe` Right (Match annz{source=("",1,1)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,4)} 0) (Ret annz{source=("",1,11)} (Number annz{source=("",1,18)} 0)) (Match annz{source=("",1,20)} (LExp (Read annz{source=("",1,1)} "_true")) (Number annz{source=("",1,28)} 1) (Ret annz{source=("",1,35)} (Number annz{source=("",1,42)} 1)) (Ret annz{source=("",1,49)} (Number annz{source=("",1,56)} 0))))

        describe "loop" $ do
            it "loop do end" $
                parse stmt_loop "loop do end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Nop annz{source=("",1,9)}))
            it "loop do v<-1 end" $
                parse stmt_loop "loop do set v<-1 end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Set annz{source=("",1,14)} False (LVar "v") (Number annz{source=("",1,16)} 1)))

-------------------------------------------------------------------------------

        describe "func:" $ do
            it "var add : ..." $
                parse stmt "var add : ((Int, Int) -> Int)"
                `shouldBe` Right (Seq annz{source = ("",1,1)} (Seq annz (Var annz{source = ("",1,1)} "add" (TypeF (TypeN [int,int]) (int),cz)) (Nop annz)) (Nop annz{source = ("",1,1)}))
            it "var add : ... <- func ..." $
                parse stmt "var add : ((Int, Int) -> Int) <- func (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Seq annz (Var annz{source=("",1,1)} "add" (TypeF (TypeN [int,int]) (int),cz)) (Nop annz)) (Set annz{source=("",1,31)} False (LVar "add") (Func annz{source=("",1,34)} (TypeF (TypeN [int,int]) (int),cz) (Seq annz{source=("",1,34)} (Seq annz (Var annz{source=("",1,34)} "a" (int,cz)) (Nop annz)) (Seq annz{source=("",1,34)} (Set annz{source=("",1,34)} False (LTuple [LVar "a",LAny]) (Arg annz{source=("",1,34)})) (Nop annz{source=("",1,70)}))))))
            it "func add : (...) do end" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (FuncS annz{source=("",1,1)} "add" (TypeF (TypeN [int,int]) (int),cz) (Seq annz{source=("",1,1)} (Seq annz{source=("",0,0)} (Var annz{source=("",1,1)} "a" (int,cz)) (Nop annz{source=("",0,0)})) (Seq annz{source=("",1,1)} (Set annz{source=("",1,1)} False (LTuple [LVar "a",LAny]) (Arg annz{source=("",1,1)})) (Nop annz{source=("",1,41)}))))
            it "func add (...) : (...)" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int)"
                `shouldBe` Left "(line 1, column 37):\nunexpected end of input\nexpecting \"where\" or \"do\""
            it "func add : (...)" $
                parse stmt_funcs "func add : ((Int, Int) -> Int)"
                `shouldBe` Right (Var annz{source=("",1,1)} "add" (TypeF (TypeN [int,int]) (int),cz))
            it "func (_,_,_) : (_,_)" $
                parse stmt_funcs "func add (_,_,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Left "(line 1, column 40):\nunexpected \"d\"\nexpecting \"where\"\narity mismatch"
            it "func (a,b,c) : (x,y)" $
                parse expr_func "func (_,_,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Left "(line 1, column 36):\nunexpected \"d\"\nexpecting \"where\"\narity mismatch"
            it "func add" $
                parse stmt_funcs "func add : ((Int, Int) -> Int) do end"
                `shouldBe` Left "(line 1, column 32):\nunexpected 'd'\nexpecting \"where\" or end of input"
            it "func add" $
                parse expr_func "func ((Int, Int) -> Int) do end"
                `shouldBe` Left "(line 1, column 18):\nunexpected \"-\"\nexpecting \")\""

            it "and" $
              (parse' stmt $
                unlines [
                  "func and (x,y) : ((Bool,Bool)->Bool) do",
                  "   return Bool.False",
                  "end",
                  "return (Bool.True) and (Bool.True)"
                 ])
              `shouldBe` Right (Seq annz (FuncS annz "and" (TypeF (TypeN [bool,bool]) (bool),cz) (Seq annz (Seq annz (Var annz "x" (bool,cz)) (Seq annz (Var annz "y" (bool,cz)) (Nop annz))) (Seq annz (Set annz False (LTuple [LVar "x",LVar "y"]) (Arg annz)) (Ret annz (Cons annz ["Bool","False"]))))) (Ret annz (Call annz (Read annz "and") (Tuple annz [Cons annz ["Bool","True"],Cons annz ["Bool","True"]]))))

        describe "data" $ do

            it "data Xxx" $
              (parse stmt "data Xxx")
              `shouldBe` Right (Data annz{source=("",1,1)} (TypeD ["Xxx"] [] Type0,cz) False)
            it "data Xxx ; var x = Xxx" $
              (parse' stmt "data Xxx ; var x:Xxx <- Xxx")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Xxx"] [] Type0,cz) False) (Seq annz (Seq annz (Var annz "x" (TypeD ["Xxx"] [] Type0,cz)) (Nop annz)) (Set annz False (LVar "x") (Cons annz ["Xxx"]))))
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (Data annz{source=("",1,1)} (TypeD ["Xxx","Yyy"] [] Type0,cz) False)
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (Data annz{source=("",1,1)} (TypeD ["Xxx","Yyy"] [] Type0,cz) False)

            it "data Xxx with ()" $
              (parse stmt "data Xxx with ()")
              `shouldBe` Right (Data annz{source=("",1,1)} (TypeD ["Xxx"] [] Type0,cz) False)

            it "data Xxx with (Int,Int)" $
              (parse stmt "data Xxx with (Int,Int)")
              `shouldBe` Right (Data annz{source=("",1,1)} (TypeD ["Xxx"] [] (TypeN [int,int]),cz) False)

            it "data Xxx with (Int)" $
              (parse' stmt "data Xxx with (Int)")
              `shouldBe` Right (Data annz (TypeD ["Xxx"] [] int,cz) False)

            it "data Xxx with Int ; x<-Xxx(1,1)" $
              (parse' stmt "data Xxx with Int ; var x:Xxx <- Xxx 1")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Xxx"] [] int,cz) False) (Seq annz (Seq annz (Var annz "x" (TypeD ["Xxx"] [] Type0,cz)) (Nop annz)) (Set annz False (LVar "x") (Call annz (Cons annz ["Xxx"]) (Number annz 1)))))

            it "TODO-fields: data Xxx (x,y) with (Int,Int)" $
              (parse stmt "data Xxx (x,y) with (Int,Int)")
              `shouldBe` Left "TODO-fields"

            it "Xxx.Yyy" $
              (parse' stmt "data Int ; data Xxx with Int ; data Xxx.Yyy with Int ; var y:Xxx.Yyy <- Xxx.Yyy (1,2)")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Int"] [] Type0,M.fromList []) False) (Seq annz (Data annz (TypeD ["Xxx"] [] int,M.fromList []) False) (Seq annz (Data annz (TypeD ["Xxx","Yyy"] [] int,M.fromList []) False) (Seq annz (Seq annz (Var annz "y" (TypeD ["Xxx","Yyy"] [] Type0,M.fromList [])) (Nop annz)) (Set annz False (LVar "y") (Call annz (Cons annz ["Xxx","Yyy"]) (Tuple annz [Number annz 1,Number annz 2])))))))

            it "data X with Int ; x:Int ; X x <- X 1 ; ret x" $
              (parse' stmt "data Xxx with Int ; var x:Int ; set Xxx x <- Xxx 1 ; return x")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Xxx"] [] int,cz) False) (Seq annz (Seq annz (Seq annz (Var annz "x" (int,cz)) (Nop annz)) (Nop annz)) (Seq annz (Set annz False (LCons ["Xxx"] (LVar "x")) (Call annz (Cons annz ["Xxx"]) (Number annz 1))) (Ret annz (Read annz "x")))))
            it "data X with Int ; X 1 <- X 1 ; return 1" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 <- Xxx 1 ; return 1")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (LCons ["Xxx"] (LNumber 1)) (Call annz (Cons annz ["Xxx"]) (Number annz 1))) (Ret annz (Number annz 1))))
            it "data X with Int ; x:Int ; X 1 <- X 2" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 <- Xxx 2 ; return 2")
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (LCons ["Xxx"] (LNumber 1)) (Call annz (Cons annz ["Xxx"]) (Number annz 2))) (Ret annz (Number annz 2))))

            it "Aa <- Aa.Bb" $
              (parse' stmt $
                unlines [
                  "data Aa with Int",
                  "data Aa.Bb",
                  "var b : Aa.Bb <- Aa.Bb 1",
                  "var a : Aa <- b",
                  "var v : Int",
                  "set (Aa v) <- b",
                  "return v"
                ])
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Aa"] [] int,cz) False) (Seq annz (Data annz (TypeD ["Aa","Bb"] [] Type0,cz) False) (Seq annz (Seq annz (Seq annz (Var annz "b" (TypeD ["Aa","Bb"] [] Type0,cz)) (Nop annz)) (Set annz False (LVar "b") (Call annz (Cons annz ["Aa","Bb"]) (Number annz 1)))) (Seq annz (Seq annz (Seq annz (Var annz "a" (TypeD ["Aa"] [] Type0,cz)) (Nop annz)) (Set annz False (LVar "a") (Read annz "b"))) (Seq annz (Seq annz (Seq annz (Var annz "v" (int,cz)) (Nop annz)) (Nop annz)) (Seq annz (Set annz False (LCons ["Aa"] (LVar "v")) (Read annz "b")) (Ret annz (Read annz "v"))))))))

        describe "data - constraint:" $ do

            it "Unit a/IEq" $
              parse' stmt "data Unit for a with a where a is IEq"
              `shouldBe` Right (Data annz (TypeD ["Unit"] [TypeV "a"] (TypeV "a"),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,a)" $
              parse' stmt "data Pair for a with (a,a)"
              `shouldBe` Right (Data annz (TypeD ["Pair"] [TypeV "a"] (TypeN [TypeV "a",TypeV "a"]),M.fromList []) False)
            it "Pair (a,a)/IEq" $
              parse' stmt "data Pair for a with (a,a) where (a is IEq)"
              `shouldBe` Right (Data annz (TypeD ["Pair"] [TypeV "a"] (TypeN [TypeV "a",TypeV "a"]),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,b)" $
              parse' stmt "data Pair for (a,b) with (a,b)"
              `shouldBe` Right (Data annz (TypeD ["Pair"] [TypeV "a",TypeV "b"] (TypeN [TypeV "a",TypeV "b"]),M.fromList []) False)
            it "Pair (a,b)/IEq" $
              parse' stmt "data Pair for (a,b) with (a,b) where (a is IEq, b is IEq)"
              `shouldBe` Right (Data annz (TypeD ["Pair"] [TypeV "a",TypeV "b"] (TypeN [TypeV "a",TypeV "b"]),M.fromList [("a",S.fromList ["IEq"]),("b",S.fromList ["IEq"])]) False)

            it "Pair (a,a) ; p1:Pair(Int,Int)" $
              parse' stmt "data Pair for a with (a,a) ; var p1 : Pair of Int"
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Pair"] [TypeV "a"] (TypeN [TypeV "a",TypeV "a"]),M.fromList []) False) (Seq annz (Seq annz (Var annz "p1" (TypeD ["Pair"] [int] Type0,M.fromList [])) (Nop annz)) (Nop annz)))

            it "Either" $
              parse' stmt "data Either for (a,b) ; data Either.Left  with a ; data Either.Right with b"
              `shouldBe` Right (Seq annz (Data annz (TypeD ["Either"] [TypeV "a",TypeV "b"] Type0,M.fromList []) False) (Seq annz (Data annz (TypeD ["Either","Left"] [] (TypeV "a"),M.fromList []) False) (Data annz (TypeD ["Either","Right"] [] (TypeV "b"),M.fromList []) False)))

        describe "constraint:" $ do

          it "Int ; IF3able a ; inst IF3able Int ; return f3 1" $
            (parse stmt $
              unlines [
                "constraint IF3able for a with"  ,
                " var f3 : (a -> Int)"          ,
                "end"                           ,
                "instance of (IF3able for Int) with" ,
                " func f3 (v) : (a -> Int) do"  ,
                "   return v"                   ,
                " end"                          ,
                "end"                           ,
                "return f3(10)"
              ])
            `shouldBe` Right
              (Seq annz{source=("",1,1)}
              (Class annz{source=("",1,1)} "IF3able" (cv "a")
                (Seq annz{source=("",2,2)}
                (Seq annz{source=("",0,0)}
                (Var annz{source=("",2,2)} "f3" (TypeF (TypeV "a") (int),cz))
                (Nop annz{source=("",0,0)}))
                (Nop annz{source=("",2,2)})))
              (Seq annz{source=("",1,1)}
              (Inst annz{source=("",4,1)} "IF3able" (int,cz)
                (FuncS annz{source=("",5,2)} "f3" (TypeF (TypeV "a") (int),cz)
                  (Seq annz{source=("",5,2)}
                  (Seq annz{source=("",0,0)}
                  (Var annz{source=("",5,2)} "v" (TypeV "a",cz))
                  (Nop annz{source=("",0,0)}))
                  (Seq annz{source=("",5,2)}
                  (Set annz{source=("",5,2)} False (LVar "v") (Arg annz{source=("",5,2)})) (Ret annz{source=("",6,4)} (Read annz{source=("",6,11)} "v"))))))
              (Ret annz{source=("",9,1)} (Call annz{source=("",9,8)} (Read annz{source=("",9,8)} "f3") (Number annz{source=("",9,11)} 10)))))

          it "IOrd extends IEq" $
            (parse' stmt $
              unlines [
                "constraint (IEq for a) with",
                "   func == : ((a,a) -> Bool)",
                "end",
                "",
                "constraint (IOrd for a) where (a is IEq) with",
                "   func >= : ((a,a) -> Bool)",
                "end",
                "",
                "instance of IEq for Bool with",
                "   func == (x,y) : ((a,a) -> Bool) do return Bool.True end",
                "end",
                "",
                "instance of (IOrd for Bool) with",
                "   func >= (x,y) : ((a,a) -> Bool) do return Bool.True end",
                "end",
                "",
                "return (Bool.True) >= (Bool.False)"
              ])
            `shouldBe` Right
              (Seq annz
              (Class annz "IEq" (cv "a")
                (Var annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz)))
              (Seq annz
              (Class annz "IOrd" (cvc("a","IEq"))
                (Var annz ">=" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz)))
              (Seq annz
              (Inst annz "IEq" (bool,cz)
                (FuncS annz "==" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz)
                  (Seq annz (Seq annz (Var annz "x" (TypeV "a",cz)) (Seq annz (Var annz "y" (TypeV "a",cz)) (Nop annz))) (Seq annz (Set annz False (LTuple [LVar "x",LVar "y"]) (Arg annz)) (Ret annz (Cons annz ["Bool","True"]))))))
              (Seq annz
              (Inst annz "IOrd" (bool,cz)
                (FuncS annz ">=" (TypeF (TypeN [TypeV "a",TypeV "a"]) (bool),cz)
                  (Seq annz (Seq annz (Var annz "x" (TypeV "a",cz)) (Seq annz (Var annz "y" (TypeV "a",cz)) (Nop annz))) (Seq annz (Set annz False (LTuple [LVar "x",LVar "y"]) (Arg annz)) (Ret annz (Cons annz ["Bool","True"]))))))
              (Ret annz (Call annz (Read annz ">=") (Tuple annz [Cons annz ["Bool","True"],Cons annz ["Bool","False"]])))))))

          it "IFable f ; g a is IFable" $
            (parse' stmt $ "var x : a where (a is IFable,b is IFable)") -- (a,b) vs (IFable), arity mismatch
            `shouldBe` Right (Seq annz (Seq annz (Var annz "x" (TypeV "a",M.fromList [("a",S.fromList ["IFable"]),("b",S.fromList ["IFable"])])) (Nop annz)) (Nop annz))

          it "IFable f ; g a is IFable" $
            (parse' stmt $
              unlines [
                "constraint IFable for a with",
                "   func f : (a -> Bool)",
                "end",
                "",
                "func g x : (a -> Bool) where a is IFable do",
                "   return f x",
                "end",
                "",
                --"var h : (a -> Bool) where a is IFable",
                --"set h <- func x : (a -> Bool) where a is IFable do",
                --"   return f x",
                --"end",
                "",
                "return (g (Bool.True))"
               ])
            `shouldBe` Right
              (Seq annz
                (Class annz "IFable" (cv "a")
                  (Var annz "f" (TypeF (TypeV "a") (bool),cz)))
              (Seq annz
                (FuncS annz "g" (TypeF (TypeV "a") (bool),cvc("a","IFable"))
                  (Seq annz
                  (Seq annz
                    (Var annz "x" (TypeV "a",cvc("a","IFable"))) (Nop annz))
                  (Seq annz (Set annz False (LVar "x") (Arg annz)) (Ret annz (Call annz (Read annz "f") (Read annz "x")))))) (Ret annz (Call annz (Read annz "g") (Cons annz ["Bool","True"])))))

        describe "seq:" $ do
            it "x <- k k <- 1" $
                parse (stmt_seq ("",1,1)) "set x <- k set k <- 1"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Set annz{source=("",1,7)} False (LVar "x") (Read annz{source=("",1,10)} "k")) (Set annz{source=("",1,18)} False (LVar "k") (Number annz{source=("",1,21)} 1)))

            it "do end; return 1" $
                parse (stmt_seq ("",1,1)) "do end return 1"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Ret annz{source=("",1,8)} (Number annz{source=("",1,15)} 1)))

            it "do end; do end; do end" $
                parse (stmt_seq ("",1,1)) "do end ; do end ; do end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Seq annz{source=("",1,1)} (Scope annz{source=("",1,10)} (Nop annz{source=("",1,13)})) (Scope annz{source=("",1,19)} (Nop annz{source=("",1,22)}))))

            it "var a:Int ; a<-1" $
                parse (stmt_seq ("",1,1)) "var a:Int ; set a<-1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Set (annz{source = ("",1,18)}) False (LVar "a") (Number (annz{source = ("",1,20)}) 1)))

        describe "stmt:" $ do
            it "var x:Int; return 1" $
                parse stmt "var x:Int ;return 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Ret (annz{source = ("",1,12)}) (Number (annz{source = ("",1,19)}) 1)))

            it "var x:Int; x<-1; return x" $
                parse stmt "var x:Int ; set x <- 1 ; return x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Seq (annz{source = ("",1,1)}) (Set (annz{source = ("",1,19)}) False (LVar "x") (Number (annz{source = ("",1,22)}) 1)) (Ret (annz{source = ("",1,26)}) (Read (annz{source = ("",1,33)}) "x"))))

            it "var x:(Int,Int,)<-(1,2) ; return +x" $
                parse stmt "var x:(Int,Int)<-(1,2) ; return +x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TypeN [int,int],cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,16)}) False (LVar "x") (Tuple (annz{source = ("",1,18)}) [Number (annz{source = ("",1,19)}) 1,Number (annz{source = ("",1,21)}) 2]))) (Ret (annz{source = ("",1,26)}) (Call (annz{source = ("",1,33)}) (Read annz{source=("",1,33)} "+") (Read (annz{source = ("",1,34)}) "x"))))

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

        --parse' :: Parser Stmt -> String -> Either P.ParseError Stmt
        parse' rule src = case parse rule src of
                            Left  err  -> Left err
                            Right stmt -> Right $ clearStmt stmt
