{-# LANGUAGE QuasiQuotes #-}

module Ceu.ParserSpec (main, spec) where

import Test.Hspec
import Text.RawString.QQ
import Data.Set as S (fromList)
import Data.Map as M (fromList)

import qualified Text.Parsec as P (eof, parse)
import Text.Parsec.Prim hiding (EError)
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
import Ceu.Grammar.Full.Full    (Stmt(..), Exp(..))
import Ceu.Grammar.Full.Eval    (prelude, compile')
import qualified Ceu.Grammar.Basic as B

clearStmt :: Stmt -> Stmt
clearStmt (Class _ id  cs ifc)  = Class annz id  cs (clearStmt ifc)
clearStmt (Inst  _ cls tp imp)  = Inst  annz cls tp (clearStmt imp)
clearStmt (Data  _ tp abs)      = Data  annz tp abs
clearStmt (Var   _ var tp)      = Var   annz var tp
clearStmt (FuncS _ var tp p)    = FuncS annz var tp (clearStmt p)
clearStmt (Match _ exp cses)    = Match annz (clearExp exp)
                                    (map (\(pt,st) -> (clearExp pt, clearStmt st)) cses)
clearStmt (Set   _ chk loc exp) = Set   annz chk (clearExp loc) (clearExp exp)
clearStmt (If    _ exp p1 p2)   = If    annz (clearExp exp) (clearStmt p1) (clearStmt p2)
clearStmt (Seq   _ p1 p2)       = Seq   annz (clearStmt p1) (clearStmt p2)
clearStmt (Loop  _ p)           = Loop  annz (clearStmt p)
clearStmt (Nop   _)             = Nop   annz
clearStmt (Scope _ p)           = Scope annz (clearStmt p)
clearStmt (Ret   _ exp)         = Ret   annz (clearExp exp)
clearStmt p                     = error $ "clearStmt: unexpected statement: " ++ (show p)

clearExp :: Exp -> Exp
clearExp (EAny   _)       = EAny   annz
clearExp (ECons  _ v)     = ECons  annz v
clearExp (EVar   _ v)     = EVar   annz v
clearExp (EArg   _)       = EArg   annz
clearExp (EUnit  _)       = EUnit  annz
clearExp (ETuple _ es)    = ETuple annz (map clearExp es)
clearExp (EFunc  _ tp p)  = EFunc  annz tp (clearStmt p)
clearExp (ECall  _ e1 e2) = ECall  annz (clearExp e1) (clearExp e2)

fromRight' :: Either a b -> b
fromRight' (Right x) = x

int  = TData ["Int"]  [] TUnit
bool = TData ["Bool"] [] TUnit

mmm z loc exp p1 p2 = Match z exp [(loc,p1),(EAny z,p2)]

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
                `shouldBe` Right "->" --Left "(line 1, column 3):\nunexpected symbol\nexpecting operator"

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
                `shouldBe` Right TUnit
            it "( )" $
                parse type_0 "( )"
                `shouldBe` Right TUnit
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
                `shouldBe` Right (TData ["III"] [] TUnit)
            it "int" $
                parse type_D "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "Int of ()" $
                parse type_D "Int of ()"
                `shouldBe` Right (int)
            it "Int of Int of Int" $
                parse type_D "Int of Int of Int"
                `shouldBe` Right (TData ["Int"] [TData ["Int"] [int] TUnit] TUnit)
            it "Tree of (Int,Int)" $
                parse type_D "Tree of (Int,Int)"
                `shouldBe` Right (TData ["Tree"] [int, int] TUnit)
        describe "typeN" $ do
            it "()" $
                parse type_N "()"
                `shouldBe` Left "(line 1, column 2):\nunexpected \")\"\nexpecting type"
            it "(Int)" $
                parse type_N "(Int)"
                `shouldBe` Left "(line 1, column 5):\nunexpected \")\"\nexpecting data identifier, \".\", \"of\" or \",\""
            it "(Int,Int)" $
                parse type_N "(Int,Int)"
                `shouldBe` Right (TTuple [int, int])
            it "(Int,())" $
                parse type_N "(Int,())"
                `shouldBe` Right (TTuple [int, TUnit])

        describe "typeF" $ do
            it "(Int -> Int)" $
                parse type_F "(Int -> Int)"
                `shouldBe` Right (TFunc (int) (int))
            it "(a -> Int)" $
                parse type_F "(a -> Int)"
                `shouldBe` Right (TFunc (TAny "a") (int))
            it "a -> Int" $
                parse type_F "a -> Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"a\"\nexpecting \"(\""

        describe "typeV" $ do
            it "Int" $
                parse type_V "Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"I\""
            it "a" $
                parse type_V "a"
                `shouldBe` Right (TAny "a")

        describe "pType" $ do
            it "()" $
                parse pType "()"
                `shouldBe` Right TUnit
            it "Int" $
                parse pType "Int"
                `shouldBe` Right (int)
            it "(Int, ((),()))" $
                parse pType "(Int, ((),()))"
                `shouldBe` Right (TTuple [int, TTuple [TUnit,TUnit]])

    describe "expr:" $ do
        describe "const:" $ do
            it "0" $
                parse expr_number "0"
                `shouldBe` Right (ECons annz{source=("",1,1)} ["Int","0"])
        describe "read:" $ do
            it "a" $
                parse expr_read "a"
                `shouldBe` Right (EVar annz{source=("",1,1)} "a")
            it "aaa" $
                parse expr_read "aaa"
                `shouldBe` Right (EVar annz{source=("",1,1)} "aaa")
        describe "umn:" $ do
            it "-1" $
                parse expr "-1"
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "negate") (ECons annz{source=("",1,2)} ["Int","1"]))
            it "--1" $
                parse expr "--1"
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "--") (ECons annz{source=("",1,3)} ["Int","1"]))
        describe "parens:" $ do
            it "(1)" $
                parse expr_parens "(1)"
                `shouldBe` Right (ECons annz{source=("",1,2)} ["Int","1"])
            it "((- +1))" $
                parse expr_parens "((- +1))"
                `shouldBe` Right (ECall annz{source=("",1,5)} (EVar annz{source=("",1,5)} "+") (ETuple annz{source=("",1,3)} [EVar annz{source=("",1,3)} "-",ECons annz{source=("",1,6)} ["Int","1"]]))
            it "(- (-1))" $
                parse expr_parens "(- (+1))"
                `shouldBe` Right (ECall annz{source=("",1,2)} (EVar annz{source=("",1,2)} "negate") (ECall annz{source=("",1,5)} (EVar annz{source=("",1,5)} "+") (ECons annz{source=("",1,6)} ["Int","1"])))
        describe "add_sub:" $ do
            it "1+1" $
                parse expr "1+1"
                `shouldBe` Right (ECall annz{source=("",1,2)} (EVar annz{source=("",1,2)} "+") (ETuple annz{source=("",1,1)} [(ECons annz{source=("",1,1)} ["Int","1"]), (ECons annz{source=("",1,3)} ["Int","1"])]))
        describe "mul_div:" $ do
            it "1*1" $
                parse expr "1*1"
                `shouldBe` Right (ECall annz{source=("",1,2)} (EVar annz{source=("",1,2)} "*") (ETuple annz{source=("",1,1)} [(ECons annz{source=("",1,1)} ["Int","1"]), (ECons annz{source=("",1,3)} ["Int","1"])]))
            it "(1*2)*3" $
                parse expr "(1 * 2)*3"
                `shouldBe` Right (ECall annz{source=("",1,8)} (EVar annz{source=("",1,8)} "*") (ETuple annz{source=("",1,4)} [(ECall annz{source=("",1,4)} (EVar annz{source=("",1,4)} "*") (ETuple annz{source=("",1,2)} [(ECons annz{source=("",1,2)} ["Int","1"]), (ECons annz{source=("",1,6)} ["Int","2"])])), (ECons annz{source=("",1,9)} ["Int","3"])]))

        describe "call:" $ do
            it "f 1" $
                parse expr "f 1"
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "f") (ECons annz{source=("",1,3)} ["Int","1"]))
            it "f 1" $
                parse expr "f 1"
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "f") (ECons annz{source=("",1,3)} ["Int","1"]))

        describe "tuple:" $ do
            it "(3,55,)" $ do
                parse expr_tuple "(3,55,)"
                `shouldBe` Right (ETuple annz{source=("",1,1)} [ECons annz{source=("",1,2)} ["Int","3"], ECons annz{source=("",1,4)} ["Int","55"]])

        describe "expr:" $ do
            it "0" $
                parse expr "0"
                `shouldBe` Right (ECons annz{source=("",1,1)} ["Int","0"])
            it "aaa" $
                parse expr "aaa"
                `shouldBe` Right (EVar annz{source=("",1,1)} "aaa")
            it "$1" $
                parse expr "$1"
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "$") (ECons annz{source=("",1,2)} ["Int","1"]))
            it "-1" $
                parse expr "- 1 "
                `shouldBe` Right (ECall annz{source=("",1,1)} (EVar annz{source=("",1,1)} "negate") (ECons annz{source=("",1,3)} ["Int","1"]))
            it "(aaa)" $
                parse expr "( aaa  ) "
                `shouldBe` Right (EVar annz{source=("",1,3)} "aaa")
            it "(1+2)-3" $
                parse expr "(1+2)-3"
                `shouldBe` Right (ECall annz{source=("",1,6)} (EVar annz{source=("",1,6)} "-") (ETuple annz{source=("",1,3)} [(ECall annz{source=("",1,3)} (EVar annz{source=("",1,3)} "+") (ETuple annz{source=("",1,2)} [(ECons annz{source=("",1,2)} ["Int","1"]), (ECons annz{source=("",1,4)} ["Int","2"])])), (ECons annz{source=("",1,7)} ["Int","3"])]))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (ECall annz{source=("",1,6)} (EVar annz{source=("",1,6)} "*") (ETuple annz{source=("",1,3)} [ECall annz{source=("",1,3)} (EVar annz{source=("",1,3)} "+") (ETuple annz{source=("",1,2)} [ECons annz{source=("",1,2)} ["Int","1"], ECons annz{source=("",1,4)} ["Int","2"]]), ECons annz{source=("",1,7)} ["Int","3"]]))
            it "((1+2)*3)/4" $
                parse expr "((1+2)*3)/4"
                `shouldBe` Right (ECall annz{source=("",1,10)} (EVar annz{source=("",1,10)} "/") (ETuple annz{source=("",1,7)} [ECall annz{source=("",1,7)} (EVar annz{source=("",1,7)} "*") (ETuple annz{source=("",1,4)} [ECall annz{source=("",1,4)} (EVar annz{source=("",1,4)} "+") (ETuple annz{source=("",1,3)} [ECons annz{source=("",1,3)} ["Int","1"], ECons annz{source=("",1,5)} ["Int","2"]]), ECons annz{source=("",1,8)} ["Int","3"]]), ECons annz{source=("",1,11)} ["Int","4"]]))
            it "(1+2)*3" $
                parse expr "(1+2)*3"
                `shouldBe` Right (ECall annz{source=("",1,6)} (EVar annz{source=("",1,6)} "*") (ETuple annz{source=("",1,3)} [(ECall annz{source=("",1,3)} (EVar annz{source=("",1,3)} "+") (ETuple annz{source=("",1,2)} [(ECons annz{source=("",1,2)} ["Int","1"]), (ECons annz{source=("",1,4)} ["Int","2"])])), (ECons annz{source=("",1,7)} ["Int","3"])]))

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
            it "var a: Int =  1" $
                parse stmt_var "var a : Int =  1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,1)}) False (EVar annz{source = ("",1,5)} "a") (ECons (annz{source = ("",1,16)}) ["Int","1"])))
            it "var x:() =  ()" $
                parse stmt_var "var x:() =  ()"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TUnit,cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,1)}) False (EVar annz{source = ("",1,5)} "x") (EUnit (annz{source = ("",1,13)}))))
            it "var x:(Int,()) =  (1 ())" $
                parse stmt_var "var x:(Int,()) =  (1,())"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TTuple [int,TUnit],cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,1)}) False (EVar annz{source = ("",1,5)} "x") (ETuple (annz{source = ("",1,19)}) [ECons (annz{source = ("",1,20)}) ["Int","1"],EUnit (annz{source = ("",1,22)})])))

        describe "var-tuples:" $ do
            it "((_,x,),_)" $ do
                parse (pLoc SET) "((_,x,),_)"
                `shouldBe` Right (ETuple annz{source = ("",1,1)} [ETuple annz{source = ("",1,2)} [EAny annz{source = ("",1,3)},EVar annz{source = ("",1,5)} "x"],EAny annz{source = ("",1,9)}])
            it "var (x,y) : (Int,Int) =  (1, 2); return x+y" $
                parse stmt_var "var (x,y) : (Int,Int) =  (1, 2)"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (int,cz)) (Nop (annz{source = ("",0,0)})))) (Set (annz{source = ("",1,1)}) False (ETuple annz{source = ("",1,5)} [EVar annz{source = ("",1,6)} "x",EVar annz{source = ("",1,8)} "y"]) (ETuple (annz{source = ("",1,26)}) [ECons (annz{source = ("",1,27)}) ["Int","1"], ECons (annz{source = ("",1,30)}) ["Int","2"]])))
            it "var (x,(y,_)):(Int,(Int,Int)) =  (1, (2,3)); return x+y" $
                parse stmt "var (x,(y,_)):(Int,  Int     ) =  (1, (2,3)); return x+y"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "y" (int,cz)) (Nop (annz{source = ("",0,0)})))) (Set (annz{source = ("",1,1)}) False (ETuple annz{source = ("",1,5)} [EVar annz{source = ("",1,6)} "x",ETuple annz{source = ("",1,8)} [EVar annz{source = ("",1,9)} "y",EAny annz{source = ("",1,11)}]]) (ETuple (annz{source = ("",1,35)}) [ECons (annz{source = ("",1,36)}) ["Int","1"],ETuple (annz{source = ("",1,39)}) [ ECons (annz{source = ("",1,40)}) ["Int","2"], ECons (annz{source = ("",1,42)}) ["Int","3"]]]))) (Ret (annz{source = ("",1,47)}) (ECall (annz{source = ("",1,55)}) (EVar annz{source=("",1,55)} "+") (ETuple (annz{source = ("",1,54)}) [EVar (annz{source = ("",1,54)}) "x",EVar (annz{source = ("",1,56)}) "y"]))))
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
            it "x =  1" $
                parse stmt_set "set x = 1"
                `shouldBe` Right (Set annz{source=("",1,1)} False (EVar annz{source=("",1,5)} "x") (ECons annz{source=("",1,9)} ["Int","1"]))
            it "val =  1" $
                parse stmt_set "set val = 1"
                `shouldBe` Right (Set annz{source=("",1,1)} False (EVar annz{source=("",1,5)} "val") (ECons annz{source=("",1,11)} ["Int","1"]))

        describe "call:" $ do
          it "call 1" $
            parse stmt_call "call 1"
            `shouldBe` Right (CallS annz{source = ("",1,1)} (ECons annz{source=("",1,6)} ["Int","1"]))
          it "call print" $
            parse stmt_call "call print 1"
            `shouldBe` Right (CallS (annz {source = ("",1,1)}) (ECall (annz {source = ("",1,6)}) (EVar (annz {source = ("",1,6)}) "print") (ECons (annz {source = ("",1,12)}) ["Int","1"])))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do return 1 end" $
                parse stmt_do "do return 1 end"
                `shouldBe` Right (Scope annz{source=("",1,1)} (Ret annz{source=("",1,4)} (ECons annz{source=("",1,11)} ["Int","1"])))
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
                parse stmt_if "if 0 then return ()"
                `shouldBe` Left "(line 1, column 20):\nunexpected end of input\nexpecting \"matches\", expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 then return 0" $
                parse stmt_if "if 0 then return 0"
                `shouldBe` Left "(line 1, column 19):\nunexpected end of input\nexpecting digit, \"matches\", expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 return 0 end" $
                parse stmt_if "if 0 return 0 end"
                `shouldBe` Left "(line 1, column 12):\nunexpected `return`\nexpecting expression"

            it "if 0 then return 0 else return 1 end" $
                parse stmt_if "if 0 then return 0 else return 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (Ret annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","0"])) (Ret annz{source=("",1,25)} (ECons annz{source=("",1,32)} ["Int","1"])))
            it "if 1 then return 1 end" $
                parse stmt_if "if 1 then return 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","1"]) (Ret annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","1"])) (Nop annz{source=("",1,20)}))
            it "if then return 1 end" $
                parse stmt_if "if then return 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected `then`\nexpecting expression"
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else return 1 end ; end"
                `shouldBe` Right (If annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","1"]) (If annz{source=("",1,13)} (ECons annz{source=("",1,16)} ["Int","0"]) (Nop annz{source=("",1,23)}) (Ret annz{source=("",1,28)} (ECons annz{source=("",1,35)} ["Int","1"]))) (Nop annz{source=("",1,43)}))
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else return 1 end"
                `shouldBe` Right (If annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (If annz{source=("",1,13)} (ECons annz{source=("",1,16)} ["Int","0"]) (Nop annz{source=("",1,23)}) (Nop annz{source=("",1,23)})) (Ret annz{source=("",1,34)} (ECons annz{source=("",1,41)} ["Int","1"])))
            it "if 0 then . else/if 1 then return 1 else ." $
                parse stmt_if "if 0 then return 0 else/if 1 then return 1 else return 0 end"
                `shouldBe` Right (If annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (Ret annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","0"])) (If annz{source=("",1,20)} (ECons annz{source=("",1,28)} ["Int","1"]) (Ret annz{source=("",1,35)} (ECons annz{source=("",1,42)} ["Int","1"])) (Ret annz{source=("",1,49)} (ECons annz{source=("",1,56)} ["Int","0"]))))

        describe "match" $ do
          it "match-case" $
            parse' (s *> stmt_cases) [r|
match xs with
  case List.Nil then
    return 0
  case List.Cons (=x,=xs_) then
    return 1 + (length xs_)
end
|]
            `shouldBe` Right (Match annz (EVar annz "xs") [(ECons annz ["List","Nil"],Ret annz (ECons annz ["Int","0"])),(ECall annz (ECons annz ["List","Cons"]) (ETuple annz [EVar annz "x",EVar annz "xs_"]),Ret annz (ECall annz (EVar annz "+") (ETuple annz [ECons annz ["Int","1"],ECall annz (EVar annz "length") (EVar annz "xs_")]))),(EAny annz,Nop annz)])

        describe "loop" $ do
            it "loop do end" $
                parse stmt_loop "loop do end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Nop annz{source=("",1,9)}))
            it "loop do v= 1 end" $
                parse stmt_loop "loop do set v= 1 end"
                `shouldBe` Right (Loop annz{source=("",1,1)} (Set annz{source=("",1,9)} False (EVar annz{source=("",1,13)} "v") (ECons annz{source=("",1,16)} ["Int","1"])))

-------------------------------------------------------------------------------

        describe "func:" $ do
            it "var add : ..." $
                parse stmt "var add : ((Int, Int) -> Int)"
                `shouldBe` Right (Seq annz{source = ("",1,1)} (Seq annz (Var annz{source = ("",1,1)} "add" (TFunc (TTuple [int,int]) (int),cz)) (Nop annz)) (Nop annz{source = ("",1,1)}))
            it "var add : ... =  func ..." $
                parse stmt "var add : ((Int, Int) -> Int) =  func (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Seq annz (Var annz{source=("",1,1)} "add" (TFunc (TTuple [int,int]) (int),cz)) (Nop annz)) (Set annz{source=("",1,1)} False (EVar annz{source=("",1,5)} "add") (EFunc annz{source=("",1,34)} (TFunc (TTuple [int,int]) (int),cz) (Seq annz{source=("",1,34)} (Seq annz (Var annz{source=("",1,34)} "a" (int,cz)) (Nop annz)) (Seq annz{source=("",1,34)} (Set annz{source=("",1,34)} False (ETuple annz{source=("",1,39)} [EVar annz{source=("",1,40)} "a",EAny annz{source=("",1,42)}]) (EArg annz{source=("",1,34)})) (Nop annz{source=("",1,70)}))))))
            it "func add : (...) do end" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (FuncS annz{source=("",1,1)} "add" (TFunc (TTuple [int,int]) (int),cz) (Seq annz{source=("",1,1)} (Seq annz{source=("",0,0)} (Var annz{source=("",1,1)} "a" (int,cz)) (Nop annz{source=("",0,0)})) (Seq annz{source=("",1,1)} (Set annz{source=("",1,1)} False (ETuple annz{source=("",1,10)} [EVar annz{source=("",1,11)} "a",EAny annz{source=("",1,13)}]) (EArg annz{source=("",1,1)})) (Nop annz{source=("",1,41)}))))
            it "func add (...) : (...)" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int)"
                `shouldBe` Left "(line 1, column 37):\nunexpected end of input\nexpecting \"where\" or \"do\""
            it "func add : (...)" $
                parse stmt_funcs "func add : ((Int, Int) -> Int)"
                `shouldBe` Right (Var annz{source=("",1,1)} "add" (TFunc (TTuple [int,int]) (int),cz))
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
              `shouldBe` Right (Seq annz (FuncS annz "and" (TFunc (TTuple [bool,bool]) (bool),cz) (Seq annz (Seq annz (Var annz "x" (bool,cz)) (Seq annz (Var annz "y" (bool,cz)) (Nop annz))) (Seq annz (Set annz False (ETuple annz [EVar annz "x",EVar annz "y"]) (EArg annz)) (Ret annz (ECons annz ["Bool","False"]))))) (Ret annz (ECall annz (EVar annz "and") (ETuple annz [ECons annz ["Bool","True"],ECons annz ["Bool","True"]]))))

        describe "data" $ do

            it "data Xxx" $
              (parse stmt "data Xxx")
              `shouldBe` Right (Data annz{source=("",1,1)} (TData ["Xxx"] [] TUnit,cz) False)
            it "data Xxx ; var x = Xxx" $
              (parse' stmt "data Xxx ; var x:Xxx =  Xxx")
              `shouldBe` Right (Seq annz (Data annz (TData ["Xxx"] [] TUnit,cz) False) (Seq annz (Seq annz (Var annz "x" (TData ["Xxx"] [] TUnit,cz)) (Nop annz)) (Set annz False (EVar annz "x") (ECons annz ["Xxx"]))))
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (Data annz{source=("",1,1)} (TData ["Xxx","Yyy"] [] TUnit,cz) False)
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (Data annz{source=("",1,1)} (TData ["Xxx","Yyy"] [] TUnit,cz) False)

            it "data Xxx with ()" $
              (parse stmt "data Xxx with ()")
              `shouldBe` Right (Data annz{source=("",1,1)} (TData ["Xxx"] [] TUnit,cz) False)

            it "data Xxx with (Int,Int)" $
              (parse stmt "data Xxx with (Int,Int)")
              `shouldBe` Right (Data annz{source=("",1,1)} (TData ["Xxx"] [] (TTuple [int,int]),cz) False)

            it "data Xxx with (Int)" $
              (parse' stmt "data Xxx with (Int)")
              `shouldBe` Right (Data annz (TData ["Xxx"] [] int,cz) False)

            it "data Xxx with Int ; x= Xxx(1,1)" $
              (parse' stmt "data Xxx with Int ; var x:Xxx =  Xxx 1")
              `shouldBe` Right (Seq annz (Data annz (TData ["Xxx"] [] int,cz) False) (Seq annz (Seq annz (Var annz "x" (TData ["Xxx"] [] TUnit,cz)) (Nop annz)) (Set annz False (EVar annz "x") (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])))))

            it "TODO-fields: data Xxx (x,y) with (Int,Int)" $
              (parse stmt "data Xxx (x,y) with (Int,Int)")
              `shouldBe` Left "TODO-fields"

            it "Xxx.Yyy" $
              (parse' stmt "data Int ; data Xxx with Int ; data Xxx.Yyy with Int ; var y:Xxx.Yyy =  Xxx.Yyy (1,2)")
              `shouldBe` Right (Seq annz (Data annz (TData ["Int"] [] TUnit,M.fromList []) False) (Seq annz (Data annz (TData ["Xxx"] [] int,M.fromList []) False) (Seq annz (Data annz (TData ["Xxx","Yyy"] [] int,M.fromList []) False) (Seq annz (Seq annz (Var annz "y" (TData ["Xxx","Yyy"] [] TUnit,M.fromList [])) (Nop annz)) (Set annz False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","2"]])))))))

            it "data X with Int ; x:Int ; X x =  X 1 ; ret x" $
              (parse' stmt "data Xxx with Int ; var x:Int ; set Xxx x =  Xxx 1 ; return x")
              `shouldBe` Right (Seq annz (Data annz (TData ["Xxx"] [] int,cz) False) (Seq annz (Seq annz (Seq annz (Var annz "x" (int,cz)) (Nop annz)) (Nop annz)) (Seq annz (Set annz False (ECall annz (ECons annz ["Xxx"]) (EVar annz "x")) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"]))) (Ret annz (EVar annz "x")))))
            it "data X with Int ; X 1 =  X 1 ; return 1" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 =  Xxx 1 ; return 1")
              `shouldBe` Right (Seq annz (Data annz (TData ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"]))) (Ret annz (ECons annz ["Int","1"]))))
            it "data X with Int ; x:Int ; X 1 =  X 2" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 =  Xxx 2 ; return 2")
              `shouldBe` Right (Seq annz (Data annz (TData ["Xxx"] [] int,cz) False) (Seq annz (Set annz False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"]))) (Ret annz (ECons annz ["Int","2"]))))

            it "Aa =  Aa.Bb" $
              (parse' stmt $
                unlines [
                  "data Aa with Int",
                  "data Aa.Bb",
                  "var b : Aa.Bb =  Aa.Bb 1",
                  "var a : Aa =  b",
                  "var v : Int",
                  "set (Aa v) =  b",
                  "return v"
                ])
              `shouldBe` Right (Seq annz (Data annz (TData ["Aa"] [] int,cz) False) (Seq annz (Data annz (TData ["Aa","Bb"] [] TUnit,cz) False) (Seq annz (Seq annz (Seq annz (Var annz "b" (TData ["Aa","Bb"] [] TUnit,cz)) (Nop annz)) (Set annz False (EVar annz "b") (ECall annz (ECons annz ["Aa","Bb"]) (ECons annz ["Int","1"])))) (Seq annz (Seq annz (Seq annz (Var annz "a" (TData ["Aa"] [] TUnit,cz)) (Nop annz)) (Set annz False (EVar annz "a") (EVar annz "b"))) (Seq annz (Seq annz (Seq annz (Var annz "v" (int,cz)) (Nop annz)) (Nop annz)) (Seq annz (Set annz False (ECall annz (ECons annz ["Aa"]) (EVar annz "v")) (EVar annz "b")) (Ret annz (EVar annz "v"))))))))

        describe "data - constraint:" $ do

            it "EUnit a/IEq" $
              parse' stmt "data EUnit for a with a where a is IEq"
              `shouldBe` Right (Data annz (TData ["EUnit"] [TAny "a"] (TAny "a"),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,a)" $
              parse' stmt "data Pair for a with (a,a)"
              `shouldBe` Right (Data annz (TData ["Pair"] [TAny "a"] (TTuple [TAny "a",TAny "a"]),M.fromList []) False)
            it "Pair (a,a)/IEq" $
              parse' stmt "data Pair for a with (a,a) where (a is IEq)"
              `shouldBe` Right (Data annz (TData ["Pair"] [TAny "a"] (TTuple [TAny "a",TAny "a"]),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,b)" $
              parse' stmt "data Pair for (a,b) with (a,b)"
              `shouldBe` Right (Data annz (TData ["Pair"] [TAny "a",TAny "b"] (TTuple [TAny "a",TAny "b"]),M.fromList []) False)
            it "Pair (a,b)/IEq" $
              parse' stmt "data Pair for (a,b) with (a,b) where (a is IEq, b is IEq)"
              `shouldBe` Right (Data annz (TData ["Pair"] [TAny "a",TAny "b"] (TTuple [TAny "a",TAny "b"]),M.fromList [("a",S.fromList ["IEq"]),("b",S.fromList ["IEq"])]) False)

            it "Pair (a,a) ; p1:Pair(Int,Int)" $
              parse' stmt "data Pair for a with (a,a) ; var p1 : Pair of Int"
              `shouldBe` Right (Seq annz (Data annz (TData ["Pair"] [TAny "a"] (TTuple [TAny "a",TAny "a"]),M.fromList []) False) (Seq annz (Seq annz (Var annz "p1" (TData ["Pair"] [int] TUnit,M.fromList [])) (Nop annz)) (Nop annz)))

            it "Either" $
              parse' stmt "data Either for (a,b) ; data Either.Left  with a ; data Either.Right with b"
              `shouldBe` Right (Seq annz (Data annz (TData ["Either"] [TAny "a",TAny "b"] TUnit,M.fromList []) False) (Seq annz (Data annz (TData ["Either","Left"] [] (TAny "a"),M.fromList []) False) (Data annz (TData ["Either","Right"] [] (TAny "b"),M.fromList []) False)))

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
                (Var annz{source=("",2,2)} "f3" (TFunc (TAny "a") (int),cz))
                (Nop annz{source=("",0,0)}))
                (Nop annz{source=("",2,2)})))
              (Seq annz{source=("",1,1)}
              (Inst annz{source=("",4,1)} "IF3able" (int,cz)
                (FuncS annz{source=("",5,2)} "f3" (TFunc (TAny "a") (int),cz)
                  (Seq annz{source=("",5,2)}
                  (Seq annz{source=("",0,0)}
                  (Var annz{source=("",5,2)} "v" (TAny "a",cz))
                  (Nop annz{source=("",0,0)}))
                  (Seq annz{source=("",5,2)}
                  (Set annz{source=("",5,2)} False (EVar annz{source=("",5,11)} "v") (EArg annz{source=("",5,2)})) (Ret annz{source=("",6,4)} (EVar annz{source=("",6,11)} "v"))))))
              (Ret annz{source=("",9,1)} (ECall annz{source=("",9,8)} (EVar annz{source=("",9,8)} "f3") (ECons annz{source=("",9,11)} ["Int","10"])))))

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
                (Var annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz)))
              (Seq annz
              (Class annz "IOrd" (cvc("a","IEq"))
                (Var annz ">=" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz)))
              (Seq annz
              (Inst annz "IEq" (bool,cz)
                (FuncS annz "==" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz)
                  (Seq annz (Seq annz (Var annz "x" (TAny "a",cz)) (Seq annz (Var annz "y" (TAny "a",cz)) (Nop annz))) (Seq annz (Set annz False (ETuple annz [EVar annz "x",EVar annz "y"]) (EArg annz)) (Ret annz (ECons annz ["Bool","True"]))))))
              (Seq annz
              (Inst annz "IOrd" (bool,cz)
                (FuncS annz ">=" (TFunc (TTuple [TAny "a",TAny "a"]) (bool),cz)
                  (Seq annz (Seq annz (Var annz "x" (TAny "a",cz)) (Seq annz (Var annz "y" (TAny "a",cz)) (Nop annz))) (Seq annz (Set annz False (ETuple annz [EVar annz "x",EVar annz "y"]) (EArg annz)) (Ret annz (ECons annz ["Bool","True"]))))))
              (Ret annz (ECall annz (EVar annz ">=") (ETuple annz [ECons annz ["Bool","True"],ECons annz ["Bool","False"]])))))))

          it "IFable f ; g a is IFable" $
            (parse' stmt $ "var x : a where (a is IFable,b is IFable)") -- (a,b) vs (IFable), arity mismatch
            `shouldBe` Right (Seq annz (Seq annz (Var annz "x" (TAny "a",M.fromList [("a",S.fromList ["IFable"]),("b",S.fromList ["IFable"])])) (Nop annz)) (Nop annz))

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
                --"set h =  func x : (a -> Bool) where a is IFable do",
                --"   return f x",
                --"end",
                "",
                "return (g (Bool.True))"
               ])
            `shouldBe` Right
              (Seq annz
                (Class annz "IFable" (cv "a")
                  (Var annz "f" (TFunc (TAny "a") (bool),cz)))
              (Seq annz
                (FuncS annz "g" (TFunc (TAny "a") (bool),cvc("a","IFable"))
                  (Seq annz
                  (Seq annz
                    (Var annz "x" (TAny "a",cvc("a","IFable"))) (Nop annz))
                  (Seq annz (Set annz False (EVar annz "x") (EArg annz)) (Ret annz (ECall annz (EVar annz "f") (EVar annz "x")))))) (Ret annz (ECall annz (EVar annz "g") (ECons annz ["Bool","True"])))))

        describe "seq:" $ do
            it "x =  k k =  1" $
                parse (stmt_seq ("",1,1)) "set x =  k set k =  1"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Set annz{source=("",1,1)} False (EVar annz{source = ("",1,5)} "x") (EVar annz{source=("",1,10)} "k")) (Set annz{source=("",1,12)} False (EVar annz{source = ("",1,16)} "k") (ECons annz{source=("",1,21)} ["Int","1"])))

            it "do end; return 1" $
                parse (stmt_seq ("",1,1)) "do end return 1"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Ret annz{source=("",1,8)} (ECons annz{source=("",1,15)} ["Int","1"])))

            it "do end; do end; do end" $
                parse (stmt_seq ("",1,1)) "do end ; do end ; do end"
                `shouldBe` Right (Seq annz{source=("",1,1)} (Scope annz{source=("",1,1)} (Nop annz{source=("",1,4)})) (Seq annz{source=("",1,1)} (Scope annz{source=("",1,10)} (Nop annz{source=("",1,13)})) (Scope annz{source=("",1,19)} (Nop annz{source=("",1,22)}))))

            it "var a:Int ; a= 1" $
                parse (stmt_seq ("",1,1)) "var a:Int ; set a = 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "a" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Set (annz{source = ("",1,13)}) False (EVar annz{source = ("",1,17)} "a") (ECons (annz{source = ("",1,21)}) ["Int","1"])))

        describe "stmt:" $ do
            it "var x:Int; return 1" $
                parse stmt "var x:Int ;return 1"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Ret (annz{source = ("",1,12)}) (ECons (annz{source = ("",1,19)}) ["Int","1"])))

            it "var x:Int; x= 1; return x" $
                parse stmt "var x:Int ; set x =  1 ; return x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (int,cz)) (Nop (annz{source = ("",0,0)}))) (Nop (annz{source = ("",1,1)}))) (Seq (annz{source = ("",1,1)}) (Set (annz{source = ("",1,13)}) False (EVar annz{source = ("",1,17)} "x") (ECons (annz{source = ("",1,22)}) ["Int","1"])) (Ret (annz{source = ("",1,26)}) (EVar (annz{source = ("",1,33)}) "x"))))

            it "var x:(Int,Int,)= (1,2) ; return +x" $
                parse stmt "var x:(Int,Int)= (1,2) ; return +x"
                `shouldBe` Right (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",1,1)}) (Seq (annz{source = ("",0,0)}) (Var (annz{source = ("",1,1)}) "x" (TTuple [int,int],cz)) (Nop (annz{source = ("",0,0)}))) (Set (annz{source = ("",1,1)}) False (EVar annz{source = ("",1,5)} "x") (ETuple (annz{source = ("",1,18)}) [ECons (annz{source = ("",1,19)}) ["Int","1"], ECons (annz{source = ("",1,21)}) ["Int","2"]]))) (Ret (annz{source = ("",1,26)}) (ECall (annz{source = ("",1,33)}) (EVar annz{source=("",1,33)} "+") (EVar (annz{source = ("",1,34)}) "x"))))

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
