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
import Ceu.Grammar.Type         (Type(..), FuncType(..))
import Ceu.Grammar.Ann          (annz,source,typec)
import Ceu.Grammar.Full.Full    (Stmt(..), Exp(..))
import Ceu.Grammar.Full.Eval    (prelude, compile')
import qualified Ceu.Grammar.Basic as B

clearStmt :: Stmt -> Stmt
clearStmt (SClass _ id  cs ifc)  = SClass annz id  cs (clearStmt ifc)
clearStmt (SInst  _ cls tp imp)  = SInst  annz cls tp (clearStmt imp)
clearStmt (SData  _ nms tp abs)  = SData  annz nms tp abs
clearStmt (SVar   _ var tp)      = SVar   annz var tp
clearStmt (SFunc  _ var tp pars imp)  = SFunc  annz var tp (clearExp pars) (clearStmt imp)
clearStmt (SMatch _ ini chk exp cses) = SMatch annz ini chk (clearExp exp)
                                          (map (\(ds,pt,st) -> (clearStmt ds,clearExp pt,clearStmt st)) cses)
clearStmt (SSet   _ ini chk loc exp) = SSet annz ini chk (clearExp loc) (clearExp exp)
clearStmt (SIf    _ exp p1 p2)   = SIf    annz (clearExp exp) (clearStmt p1) (clearStmt p2)
clearStmt (SSeq   _ p1 p2)       = SSeq   annz (clearStmt p1) (clearStmt p2)
clearStmt (SLoop  _ p)           = SLoop  annz (clearStmt p)
clearStmt (SNop   _)             = SNop   annz
clearStmt (SScope _ p)           = SScope annz (clearStmt p)
clearStmt (SRet   _ exp)         = SRet   annz (clearExp exp)
clearStmt p                     = error $ "clearStmt: unexpected statement: " ++ (show p)

clearExp :: Exp -> Exp
clearExp (EAny   _)       = EAny   annz
clearExp (ECons  _ v)     = ECons  annz v
clearExp (EVar   _ v)     = EVar   annz v
clearExp (EArg   _)       = EArg   annz
clearExp (EUnit  _)       = EUnit  annz
clearExp (ETuple _ es)    = ETuple annz (map clearExp es)
clearExp (EFunc  _ tp pars imp) = EFunc  annz tp (clearExp pars) (clearStmt imp)
clearExp (ECall  _ e1 e2) = ECall  annz (clearExp e1) (clearExp e2)

fromRight' :: Either a b -> b
fromRight' (Right x) = x

int  = TData False ["Int"]  [] (TUnit False)
int' = TData True  ["Int"]  [] (TUnit False)
bool = TData False ["Bool"] [] (TUnit False)

mmm z loc exp p1 p2 = SMatch z True False exp [(SNop z,loc,p1),(SNop z,EAny z,p2)]

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
                parse (type_0 False) "()"
                `shouldBe` Right (TUnit False)
            it "( )" $
                parse (type_0 False) "( )"
                `shouldBe` Right (TUnit False)
            it "(())" $
                parse (type_0 False) "(())"
                `shouldBe` Left "(line 1, column 2):\nunexpected \"(\"\nexpecting \")\""
        describe "typeD" $ do
            it "Int" $
                parse (type_D False) "Int"
                `shouldBe` Right (int)
            it "III" $
                parse (type_D False) "III"
                --`shouldBe` Left "(line 1, column 4):\nunexpected uppercase identifier\nexpecting data identifier"
                `shouldBe` Right (TData False ["III"] [] (TUnit False))
            it "int" $
                parse (type_D False) "int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"i\""
            it "Int of ()" $
                parse (type_D False) "Int of ()"
                `shouldBe` Right (int)
            it "Int of Int of Int" $
                parse (type_D False) "Int of Int of Int"
                `shouldBe` Right (TData False ["Int"] [TData False ["Int"] [int] (TUnit False)] (TUnit False))
            it "Tree of (Int,Int)" $
                parse (type_D False) "Tree of (Int,Int)"
                `shouldBe` Right (TData False ["Tree"] [int, int] (TUnit False))
        describe "typeN" $ do
            it "()" $
                parse (type_N False) "()"
                `shouldBe` Left "(line 1, column 2):\nunexpected \")\"\nexpecting type"
            it "(Int)" $
                parse (type_N False) "(Int)"
                `shouldBe` Left "(line 1, column 5):\nunexpected \")\"\nexpecting data identifier, \".\", \"of\" or \",\""
            it "(Int,Int)" $
                parse (type_N False) "(Int,Int)"
                `shouldBe` Right (TTuple False [int, int])
            it "(Int,())" $
                parse (type_N False) "(Int,())"
                `shouldBe` Right (TTuple False [int, (TUnit False)])

        describe "typeF" $ do
            it "(Int -> Int)" $
                parse (type_F False) "(Int -> Int)"
                `shouldBe` Right (TFunc False FuncUnknown (int) (int))
            it "(a -> Int)" $
                parse (type_F False) "(a -> Int)"
                `shouldBe` Right (TFunc False FuncUnknown (TVar False "a") (int))
            it "a -> Int" $
                parse (type_F False) "a -> Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"a\"\nexpecting \"(\""

        describe "typeV" $ do
            it "Int" $
                parse (type_V False) "Int"
                `shouldBe` Left "(line 1, column 1):\nunexpected \"I\""
            it "a" $
                parse (type_V False) "a"
                `shouldBe` Right (TVar False "a")

        describe "pType" $ do
            it "()" $
                parse pType "()"
                `shouldBe` Right (TUnit False)
            it "Int" $
                parse pType "Int"
                `shouldBe` Right (int)
            it "(Int, ((),()))" $
                parse pType "(Int, ((),()))"
                `shouldBe` Right (TTuple False [int, TTuple False [(TUnit False),(TUnit False)]])

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

        describe "field:" $ do
            it "X._1" $ do
                parse expr_field "X._1"
                `shouldBe` Right (EField annz{source = ("",1,1)} ["X"] "_1")
            it "X._1._2" $ do
                parse expr_field "X._1._2"
                `shouldBe` Left "(line 1, column 5):\nunexpected '.'\nexpecting digit or end of input"

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
            it "1 + X._1 x" $
                parse expr "1 + (X._1 x)"
                `shouldBe` Right (ECall (annz{source = ("",1,3)}) (EVar (annz{source = ("",1,3)}) "+") (ETuple (annz{source = ("",1,1)}) [ECons (annz{source = ("",1,1)}) ["Int","1"],ECall (annz{source = ("",1,6)}) (EField (annz{source = ("",1,6)}) ["X"] "_1") (EVar (annz{source = ("",1,11)}) "x")]))

    describe "stmt:" $ do
        describe "nop:" $ do
            it "-" $
                parse stmt_nop ""
                `shouldBe` Right (SNop annz{source=("",1,1)})

        describe "var:" $ do
            it "var x: Int" $
                parse stmt_var "var x: Int;"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int,cz)) (SNop (annz{source = ("",0,0)}))) (SNop (annz{source = ("",1,1)})))
            it "var val x" $
                parse stmt_var "var val x"
                `shouldBe` Left "(line 1, column 9):\nunexpected \"x\"\nexpecting \":\""
            it "var a: Int =  1" $
                parse stmt_var "var a : Int =  1"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "a" (int,cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "a") (ECons (annz{source = ("",1,16)}) ["Int","1"])))
            it "var x:() =  ()" $
                parse stmt_var "var x:() =  ()"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" ((TUnit False),cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "x") (EUnit (annz{source = ("",1,13)}))))
            it "var x:(Int,()) =  (1 ())" $
                parse stmt_var "var x:(Int,()) =  (1,())"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (TTuple False [int,(TUnit False)],cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "x") (ETuple (annz{source = ("",1,19)}) [ECons (annz{source = ("",1,20)}) ["Int","1"],EUnit (annz{source = ("",1,22)})])))

        describe "ref:" $ do
            it "var x: ref Int" $
                parse stmt_var "var x: ref Int;"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int',cz)) (SNop (annz{source = ("",0,0)}))) (SNop (annz{source = ("",1,1)})))
            it "var a: ref Int =  1" $
                parse stmt_var "var a : ref Int =  1"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "a" (int',cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "a") (ECons (annz{source = ("",1,20)}) ["Int","1"])))
            it "var x: ref () =  ()" $
                parse stmt_var "var x: ref () =  ()"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" ((TUnit True),cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "x") (EUnit (annz{source = ("",1,18)}))))
            it "var x:(ref Int,()) =  (1 ())" $
                parse stmt_var "var x:(ref Int,()) =  (1,())"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (TTuple False [int',(TUnit False)],cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "x") (ETuple (annz{source = ("",1,23)}) [ECons (annz{source = ("",1,24)}) ["Int","1"],EUnit (annz{source = ("",1,26)})])))

        describe "var-tuples:" $ do
            it "((_,x,),_)" $ do
                parse (pPat SET) "((_,x,),_)"
                `shouldBe` Right (ETuple annz{source = ("",1,1)} [ETuple annz{source = ("",1,2)} [EAny annz{source = ("",1,3)},EVar annz{source = ("",1,5)} "x"],EAny annz{source = ("",1,9)}])
            it "var (x,y) : (Int,Int) =  (1, 2); return x+y" $
                parse stmt_var "var (x,y) : (Int,Int) =  (1, 2)"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int,cz)) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "y" (int,cz)) (SNop (annz{source = ("",0,0)})))) (SSet (annz{source = ("",1,1)}) True False (ETuple annz{source = ("",1,5)} [EVar annz{source = ("",1,6)} "x",EVar annz{source = ("",1,8)} "y"]) (ETuple (annz{source = ("",1,26)}) [ECons (annz{source = ("",1,27)}) ["Int","1"], ECons (annz{source = ("",1,30)}) ["Int","2"]])))
            it "var (x,(y,_)):(Int,(Int,Int)) =  (1, (2,3)); return x+y" $
                parse stmt "var (x,(y,_)):(Int,  Int     ) =  (1, (2,3)); return x+y"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int,cz)) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "y" (int,cz)) (SNop (annz{source = ("",0,0)})))) (SSet (annz{source = ("",1,1)}) True False (ETuple annz{source = ("",1,5)} [EVar annz{source = ("",1,6)} "x",ETuple annz{source = ("",1,8)} [EVar annz{source = ("",1,9)} "y",EAny annz{source = ("",1,11)}]]) (ETuple (annz{source = ("",1,35)}) [ECons (annz{source = ("",1,36)}) ["Int","1"],ETuple (annz{source = ("",1,39)}) [ ECons (annz{source = ("",1,40)}) ["Int","2"], ECons (annz{source = ("",1,42)}) ["Int","3"]]]))) (SRet (annz{source = ("",1,47)}) (ECall (annz{source = ("",1,55)}) (EVar annz{source=("",1,55)} "+") (ETuple (annz{source = ("",1,54)}) [EVar (annz{source = ("",1,54)}) "x",EVar (annz{source = ("",1,56)}) "y"]))))
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
                `shouldBe` Right (SSet annz{source=("",1,1)} False False (EVar annz{source=("",1,5)} "x") (ECons annz{source=("",1,9)} ["Int","1"]))
            it "val =  1" $
                parse stmt_set "set val = 1"
                `shouldBe` Right (SSet annz{source=("",1,1)} False False (EVar annz{source=("",1,5)} "val") (ECons annz{source=("",1,11)} ["Int","1"]))

        describe "call:" $ do
          it "call 1" $
            parse stmt_call "call 1"
            `shouldBe` Right (SCall annz{source = ("",1,1)} (ECons annz{source=("",1,6)} ["Int","1"]))
          it "call print" $
            parse stmt_call "call print 1"
            `shouldBe` Right (SCall (annz {source = ("",1,1)}) (ECall (annz {source = ("",1,6)}) (EVar (annz {source = ("",1,6)}) "print") (ECons (annz {source = ("",1,12)}) ["Int","1"])))

-------------------------------------------------------------------------------

        describe "do-end:" $ do
            it "do return 1 end" $
                parse stmt_do "do return 1 end"
                `shouldBe` Right (SScope annz{source=("",1,1)} (SRet annz{source=("",1,4)} (ECons annz{source=("",1,11)} ["Int","1"])))
            it "do end" $
                parse (tk_key "do" >> stmt_nop >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse (tk_key "do" >> (try stmt_ret <|> try stmt_nop) >> tk_key "end") "do end"
                `shouldBe` Right "end"
            it "do end" $
                parse stmt_do "do end"
                `shouldBe` Right (SScope annz{source=("",1,1)} (SNop annz{source=("",1,4)}))

        describe "if-then-else/if-else" $ do
            it "if 0 then return ()" $
                parse stmt_if "if 0 then return ()"
                `shouldBe` Left "(line 1, column 20):\nunexpected end of input\nexpecting \"matches\", expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 then return 0" $
                parse stmt_if "if 0 then return 0"
                `shouldBe` Left "(line 1, column 19):\nunexpected end of input\nexpecting digit, \"matches\", expression, statement, \"else/if\", \"else\" or \"end\""

            it "if 0 return 0 end" $
                parse stmt_if "if 0 return 0 end"
                --`shouldBe` Left "(line 1, column 12):\nunexpected `return`\nexpecting expression"
                `shouldBe` Left "(line 1, column 6):\nunexpected \"r\"\nexpecting \"matches\", \"ref\" or \"then\""

            it "if 0 then return 0 else return 1 end" $
                parse stmt_if "if 0 then return 0 else return 1 end"
                `shouldBe` Right (SIf annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (SRet annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","0"])) (SRet annz{source=("",1,25)} (ECons annz{source=("",1,32)} ["Int","1"])))
            it "if 1 then return 1 end" $
                parse stmt_if "if 1 then return 1 end"
                `shouldBe` Right (SIf annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","1"]) (SRet annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","1"])) (SNop annz{source=("",1,20)}))
            it "if then return 1 end" $
                parse stmt_if "if then return 1 end"
                `shouldBe` Left "(line 1, column 8):\nunexpected `then`\nexpecting expression"
            it "if then (if then else end) end" $
                parse stmt_if "if 1 then ; if 0 then else return 1 end ; end"
                `shouldBe` Right (SIf annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","1"]) (SIf annz{source=("",1,13)} (ECons annz{source=("",1,16)} ["Int","0"]) (SNop annz{source=("",1,23)}) (SRet annz{source=("",1,28)} (ECons annz{source=("",1,35)} ["Int","1"]))) (SNop annz{source=("",1,43)}))
            it "if then (if then end) else end" $
                parse stmt_if "if 0 then ; if 0 then end ; else return 1 end"
                `shouldBe` Right (SIf annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (SIf annz{source=("",1,13)} (ECons annz{source=("",1,16)} ["Int","0"]) (SNop annz{source=("",1,23)}) (SNop annz{source=("",1,23)})) (SRet annz{source=("",1,34)} (ECons annz{source=("",1,41)} ["Int","1"])))
            it "if 0 then . else/if 1 then return 1 else ." $
                parse stmt_if "if 0 then return 0 else/if 1 then return 1 else return 0 end"
                `shouldBe` Right (SIf annz{source=("",1,1)} (ECons annz{source=("",1,4)} ["Int","0"]) (SRet annz{source=("",1,11)} (ECons annz{source=("",1,18)} ["Int","0"])) (SIf annz{source=("",1,20)} (ECons annz{source=("",1,28)} ["Int","1"]) (SRet annz{source=("",1,35)} (ECons annz{source=("",1,42)} ["Int","1"])) (SRet annz{source=("",1,49)} (ECons annz{source=("",1,56)} ["Int","0"]))))

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
            `shouldBe` Right (SMatch annz False False (EVar annz "xs") [(SNop annz,ECons annz ["List","Nil"],SRet annz (ECons annz ["Int","0"])),(SNop annz,ECall annz (ECons annz ["List","Cons"]) (ETuple annz [EVar annz "x",EVar annz "xs_"]),SRet annz (ECall annz (EVar annz "+") (ETuple annz [ECons annz ["Int","1"],ECall annz (EVar annz "length") (EVar annz "xs_")])))])

        describe "loop" $ do
            it "loop do end" $
                parse stmt_loop "loop do end"
                `shouldBe` Right (SLoop annz{source=("",1,1)} (SNop annz{source=("",1,9)}))
            it "loop do v= 1 end" $
                parse stmt_loop "loop do set v= 1 end"
                `shouldBe` Right (SLoop annz{source=("",1,1)} (SSet annz{source=("",1,9)} False False (EVar annz{source=("",1,13)} "v") (ECons annz{source=("",1,16)} ["Int","1"])))

-------------------------------------------------------------------------------

        describe "func:" $ do
            it "var add : ..." $
                parse stmt "var add : ((Int, Int) -> Int)"
                `shouldBe` Right (SSeq annz{source = ("",1,1)} (SSeq annz (SVar annz{source = ("",1,1)} "add" (TFunc False FuncUnknown (TTuple False [int,int]) (int),cz)) (SNop annz)) (SNop annz{source = ("",1,1)}))
            it "var add : ... =  func ..." $
                parse stmt "var add : ((Int, Int) -> Int) =  func (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (SSeq annz{source=("",1,1)} (SSeq annz (SVar annz{source=("",1,1)} "add" (TFunc False FuncUnknown (TTuple False [int,int]) (int),cz)) (SNop annz)) (SSet annz{source=("",1,1)} True False (EVar annz{source=("",1,5)} "add") (EFunc annz{source=("",1,34)} (TFunc False FuncUnknown (TTuple False [int,int]) (int),cz) (ETuple annz{source=("",1,39)} [EVar annz{source=("",1,40)} "a",EAny annz{source=("",1,42)}]) (SNop annz{source=("",1,70)}))))
            it "func add : (...) do end" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int) do end"
                `shouldBe` Right (SFunc annz{source=("",1,1)} "add" (TFunc False FuncUnknown (TTuple False [int,int]) (int),cz) (ETuple annz{source=("",1,10)} [EVar annz{source=("",1,11)} "a",EAny annz{source=("",1,13)}]) (SNop annz{source=("",1,41)}))
            it "func add (...) : (...)" $
                parse stmt_funcs "func add (a,_) : ((Int, Int) -> Int)"
                `shouldBe` Left "(line 1, column 37):\nunexpected end of input\nexpecting \"where\" or \"do\""
            it "func add : (...)" $
                parse stmt_funcs "func add : ((Int, Int) -> Int)"
                `shouldBe` Right (SVar annz{source=("",1,1)} "add" (TFunc False FuncUnknown (TTuple False [int,int]) (int),cz))
            it "func (_,_,_) : (_,_)" $
                parse' stmt_funcs "func add (_,_,_) : ((Int, Int) -> Int) do end"
                --`shouldBe` Left "(line 1, column 40):\nunexpected \"d\"\nexpecting \"where\"\narity mismatch"
                `shouldBe` Right (SFunc annz "add" (TFunc False FuncUnknown (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]) (TData False ["Int"] [] (TUnit False)),cz) (ETuple annz [EAny annz,EAny annz,EAny annz]) (SNop annz))
            it "func (a,b,c) : (x,y)" $
                parse'' expr_func "func (_,_,_) : ((Int, Int) -> Int) do end"
                --`shouldBe` Left "(line 1, column 36):\nunexpected \"d\"\nexpecting \"where\"\narity mismatch"
                `shouldBe` Right (EFunc annz (TFunc False FuncUnknown (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]) (TData False ["Int"] [] (TUnit False)),cz) (ETuple annz [EAny annz,EAny annz,EAny annz]) (SNop annz))
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
              `shouldBe` Right (SSeq annz (SFunc annz "and" (TFunc False FuncUnknown (TTuple False [bool,bool]) (bool),cz) (ETuple annz [EVar annz "x",EVar annz "y"]) (SRet annz (ECons annz ["Bool","False"]))) (SRet annz (ECall annz (EVar annz "and") (ETuple annz [ECons annz ["Bool","True"],ECons annz ["Bool","True"]]))))

        describe "data" $ do

            it "data Xxx" $
              (parse stmt "data Xxx")
              `shouldBe` Right (SData annz{source=("",1,1)} Nothing (TData False ["Xxx"] [] (TUnit False),cz) False)
            it "data Xxx ; var x = Xxx" $
              (parse' stmt "data Xxx ; var x:Xxx =  Xxx")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] (TUnit False),cz) False) (SSeq annz (SSeq annz (SVar annz "x" (TData False ["Xxx"] [] (TUnit False),cz)) (SNop annz)) (SSet annz True False (EVar annz "x") (ECons annz ["Xxx"]))))
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (SData annz{source=("",1,1)} Nothing (TData False ["Xxx","Yyy"] [] (TUnit False),cz) False)
            it "data Xxx.Yyy" $
              (parse stmt "data Xxx.Yyy")
              `shouldBe` Right (SData annz{source=("",1,1)} Nothing (TData False ["Xxx","Yyy"] [] (TUnit False),cz) False)

            it "data Xxx with ()" $
              (parse stmt "data Xxx with ()")
              `shouldBe` Right (SData annz{source=("",1,1)} Nothing (TData False ["Xxx"] [] (TUnit False),cz) False)

            it "data Xxx with (Int,Int)" $
              (parse stmt "data Xxx with (Int,Int)")
              `shouldBe` Right (SData annz{source=("",1,1)} Nothing (TData False ["Xxx"] [] (TTuple False [int,int]),cz) False)

            it "data Xxx with (Int)" $
              (parse' stmt "data Xxx with (Int)")
              `shouldBe` Right (SData annz Nothing (TData False ["Xxx"] [] int,cz) False)

            it "data Xxx with Int ; x= Xxx(1,1)" $
              (parse' stmt "data Xxx with Int ; var x:Xxx =  Xxx 1")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,cz) False) (SSeq annz (SSeq annz (SVar annz "x" (TData False ["Xxx"] [] (TUnit False),cz)) (SNop annz)) (SSet annz True False (EVar annz "x") (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])))))

            it "fields: data Xxx (x,y) with (Int,Int)" $
              (parse' stmt "data Xxx (x,y) with (Int,Int)")
              `shouldBe` Right (SData annz (Just ["x","y"]) (TData False ["Xxx"] [] (TTuple False [TData False ["Int"] [] (TUnit False),TData False ["Int"] [] (TUnit False)]),cz) False)

            it "Xxx.Yyy" $
              (parse' stmt "data Int ; data Xxx with Int ; data Xxx.Yyy with Int ; var y:Xxx.Yyy =  Xxx.Yyy (1,2)")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Int"] [] (TUnit False),M.fromList []) False) (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,M.fromList []) False) (SSeq annz (SData annz Nothing (TData False ["Xxx","Yyy"] [] int,M.fromList []) False) (SSeq annz (SSeq annz (SVar annz "y" (TData False ["Xxx","Yyy"] [] (TUnit False),M.fromList [])) (SNop annz)) (SSet annz True False (EVar annz "y") (ECall annz (ECons annz ["Xxx","Yyy"]) (ETuple annz [ECons annz ["Int","1"], ECons annz ["Int","2"]])))))))

            it "data X with Int ; x:Int ; X x =  X 1 ; ret x" $
              (parse' stmt "data Xxx with Int ; var x:Int ; set Xxx x =  Xxx 1 ; return x")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,cz) False) (SSeq annz (SSeq annz (SSeq annz (SVar annz "x" (int,cz)) (SNop annz)) (SNop annz)) (SSeq annz (SSet annz False False (ECall annz (ECons annz ["Xxx"]) (EVar annz "x")) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"]))) (SRet annz (EVar annz "x")))))
            it "data X with Int ; X 1 =  X 1 ; return 1" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 =  Xxx 1 ; return 1")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,cz) False) (SSeq annz (SSet annz False False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"]))) (SRet annz (ECons annz ["Int","1"]))))
            it "data X with Int ; x:Int ; X 1 =  X 2" $
              (parse' stmt "data Xxx with Int ; set Xxx 1 =  Xxx 2 ; return 2")
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Xxx"] [] int,cz) False) (SSeq annz (SSet annz False False (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","1"])) (ECall annz (ECons annz ["Xxx"]) (ECons annz ["Int","2"]))) (SRet annz (ECons annz ["Int","2"]))))

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
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Aa"] [] int,cz) False) (SSeq annz (SData annz Nothing (TData False ["Aa","Bb"] [] (TUnit False),cz) False) (SSeq annz (SSeq annz (SSeq annz (SVar annz "b" (TData False ["Aa","Bb"] [] (TUnit False),cz)) (SNop annz)) (SSet annz True False (EVar annz "b") (ECall annz (ECons annz ["Aa","Bb"]) (ECons annz ["Int","1"])))) (SSeq annz (SSeq annz (SSeq annz (SVar annz "a" (TData False ["Aa"] [] (TUnit False),cz)) (SNop annz)) (SSet annz True False (EVar annz "a") (EVar annz "b"))) (SSeq annz (SSeq annz (SSeq annz (SVar annz "v" (int,cz)) (SNop annz)) (SNop annz)) (SSeq annz (SSet annz False False (ECall annz (ECons annz ["Aa"]) (EVar annz "v")) (EVar annz "b")) (SRet annz (EVar annz "v"))))))))

        describe "data - constraint:" $ do

            it "EUnit a/IEq" $
              parse' stmt "data EUnit for a with a where a is IEq"
              `shouldBe` Right (SData annz Nothing (TData False ["EUnit"] [TVar False "a"] (TVar False "a"),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,a)" $
              parse' stmt "data Pair for a with (a,a)"
              `shouldBe` Right (SData annz Nothing (TData False ["Pair"] [TVar False "a"] (TTuple False [TVar False "a",TVar False "a"]),M.fromList []) False)
            it "Pair (a,a)/IEq" $
              parse' stmt "data Pair for a with (a,a) where (a is IEq)"
              `shouldBe` Right (SData annz Nothing (TData False ["Pair"] [TVar False "a"] (TTuple False [TVar False "a",TVar False "a"]),M.fromList [("a",S.fromList ["IEq"])]) False)
            it "Pair (a,b)" $
              parse' stmt "data Pair for (a,b) with (a,b)"
              `shouldBe` Right (SData annz Nothing (TData False ["Pair"] [TVar False "a",TVar False "b"] (TTuple False [TVar False "a",TVar False "b"]),M.fromList []) False)
            it "Pair (a,b)/IEq" $
              parse' stmt "data Pair for (a,b) with (a,b) where (a is IEq, b is IEq)"
              `shouldBe` Right (SData annz Nothing (TData False ["Pair"] [TVar False "a",TVar False "b"] (TTuple False [TVar False "a",TVar False "b"]),M.fromList [("a",S.fromList ["IEq"]),("b",S.fromList ["IEq"])]) False)

            it "Pair (a,a) ; p1:Pair(Int,Int)" $
              parse' stmt "data Pair for a with (a,a) ; var p1 : Pair of Int"
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Pair"] [TVar False "a"] (TTuple False [TVar False "a",TVar False "a"]),M.fromList []) False) (SSeq annz (SSeq annz (SVar annz "p1" (TData False ["Pair"] [int] (TUnit False),M.fromList [])) (SNop annz)) (SNop annz)))

            it "Either" $
              parse' stmt "data Either for (a,b) ; data Either.Left  with a ; data Either.Right with b"
              `shouldBe` Right (SSeq annz (SData annz Nothing (TData False ["Either"] [TVar False "a",TVar False "b"] (TUnit False),M.fromList []) False) (SSeq annz (SData annz Nothing (TData False ["Either","Left"] [] (TVar False "a"),M.fromList []) False) (SData annz Nothing (TData False ["Either","Right"] [] (TVar False "b"),M.fromList []) False)))

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
              (SSeq annz{source=("",1,1)}
              (SClass annz{source=("",1,1)} "IF3able" (cv "a")
                (SSeq annz{source=("",2,2)}
                (SSeq annz{source=("",0,0)}
                (SVar annz{source=("",2,2)} "f3" (TFunc False FuncUnknown (TVar False "a") (int),cz))
                (SNop annz{source=("",0,0)}))
                (SNop annz{source=("",2,2)})))
              (SSeq annz{source=("",1,1)}
              (SInst annz{source=("",4,1)} "IF3able" (int,cz)
                (SFunc annz{source=("",5,2)} "f3" (TFunc False FuncUnknown (TVar False "a") (int),cz) (EVar annz{source=("",5,11)} "v") (SRet annz{source=("",6,4)} (EVar annz{source=("",6,11)} "v"))))
              (SRet annz{source=("",9,1)} (ECall annz{source=("",9,8)} (EVar annz{source=("",9,8)} "f3") (ECons annz{source=("",9,11)} ["Int","10"])))))

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
              (SSeq annz
              (SClass annz "IEq" (cv "a")
                (SVar annz "==" (TFunc False FuncUnknown (TTuple False [TVar False "a",TVar False "a"]) (bool),cz)))
              (SSeq annz
              (SClass annz "IOrd" (cvc("a","IEq"))
                (SVar annz ">=" (TFunc False FuncUnknown (TTuple False [TVar False "a",TVar False "a"]) (bool),cz)))
              (SSeq annz
              (SInst annz "IEq" (bool,cz)
                (SFunc annz "==" (TFunc False FuncUnknown (TTuple False [TVar False "a",TVar False "a"]) (bool),cz) (ETuple annz [EVar annz "x",EVar annz "y"]) (SRet annz (ECons annz ["Bool","True"]))))
              (SSeq annz
              (SInst annz "IOrd" (bool,cz)
                (SFunc annz ">=" (TFunc False FuncUnknown (TTuple False [TVar False "a",TVar False "a"]) (bool),cz) (ETuple annz [EVar annz "x",EVar annz "y"]) (SRet annz (ECons annz ["Bool","True"]))))
              (SRet annz (ECall annz (EVar annz ">=") (ETuple annz [ECons annz ["Bool","True"],ECons annz ["Bool","False"]])))))))

          it "IFable f ; g a is IFable" $
            (parse' stmt $ "var x : a where (a is IFable,b is IFable)") -- (a,b) vs (IFable), arity mismatch
            `shouldBe` Right (SSeq annz (SSeq annz (SVar annz "x" (TVar False "a",M.fromList [("a",S.fromList ["IFable"]),("b",S.fromList ["IFable"])])) (SNop annz)) (SNop annz))

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
              (SSeq annz
                (SClass annz "IFable" (cv "a")
                  (SVar annz "f" (TFunc False FuncUnknown (TVar False "a") (bool),cz)))
              (SSeq annz
                (SFunc annz "g" (TFunc False FuncUnknown (TVar False "a") (bool),cvc("a","IFable")) (EVar annz "x") (SRet annz (ECall annz (EVar annz "f") (EVar annz "x")))) (SRet annz (ECall annz (EVar annz "g") (ECons annz ["Bool","True"])))))

        describe "seq:" $ do
            it "x =  k k =  1" $
                parse (stmt_seq ("",1,1)) "set x =  k set k =  1"
                `shouldBe` Right (SSeq annz{source=("",1,1)} (SSet annz{source=("",1,1)} False False (EVar annz{source = ("",1,5)} "x") (EVar annz{source=("",1,10)} "k")) (SSet annz{source=("",1,12)} False False (EVar annz{source = ("",1,16)} "k") (ECons annz{source=("",1,21)} ["Int","1"])))

            it "do end; return 1" $
                parse (stmt_seq ("",1,1)) "do end return 1"
                `shouldBe` Right (SSeq annz{source=("",1,1)} (SScope annz{source=("",1,1)} (SNop annz{source=("",1,4)})) (SRet annz{source=("",1,8)} (ECons annz{source=("",1,15)} ["Int","1"])))

            it "do end; do end; do end" $
                parse (stmt_seq ("",1,1)) "do end ; do end ; do end"
                `shouldBe` Right (SSeq annz{source=("",1,1)} (SScope annz{source=("",1,1)} (SNop annz{source=("",1,4)})) (SSeq annz{source=("",1,1)} (SScope annz{source=("",1,10)} (SNop annz{source=("",1,13)})) (SScope annz{source=("",1,19)} (SNop annz{source=("",1,22)}))))

            it "var a:Int ; a= 1" $
                parse (stmt_seq ("",1,1)) "var a:Int ; set a = 1"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "a" (int,cz)) (SNop (annz{source = ("",0,0)}))) (SNop (annz{source = ("",1,1)}))) (SSet (annz{source = ("",1,13)}) False False (EVar annz{source = ("",1,17)} "a") (ECons (annz{source = ("",1,21)}) ["Int","1"])))

        describe "stmt:" $ do
            it "var x:Int; return 1" $
                parse stmt "var x:Int ;return 1"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int,cz)) (SNop (annz{source = ("",0,0)}))) (SNop (annz{source = ("",1,1)}))) (SRet (annz{source = ("",1,12)}) (ECons (annz{source = ("",1,19)}) ["Int","1"])))

            it "var x:Int; x= 1; return x" $
                parse stmt "var x:Int ; set x =  1 ; return x"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (int,cz)) (SNop (annz{source = ("",0,0)}))) (SNop (annz{source = ("",1,1)}))) (SSeq (annz{source = ("",1,1)}) (SSet (annz{source = ("",1,13)}) False False (EVar annz{source = ("",1,17)} "x") (ECons (annz{source = ("",1,22)}) ["Int","1"])) (SRet (annz{source = ("",1,26)}) (EVar (annz{source = ("",1,33)}) "x"))))

            it "var x:(Int,Int,)= (1,2) ; return +x" $
                parse stmt "var x:(Int,Int)= (1,2) ; return +x"
                `shouldBe` Right (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",1,1)}) (SSeq (annz{source = ("",0,0)}) (SVar (annz{source = ("",1,1)}) "x" (TTuple False [int,int],cz)) (SNop (annz{source = ("",0,0)}))) (SSet (annz{source = ("",1,1)}) True False (EVar annz{source = ("",1,5)} "x") (ETuple (annz{source = ("",1,18)}) [ECons (annz{source = ("",1,19)}) ["Int","1"], ECons (annz{source = ("",1,21)}) ["Int","2"]]))) (SRet (annz{source = ("",1,26)}) (ECall (annz{source = ("",1,33)}) (EVar annz{source=("",1,33)} "+") (EVar (annz{source = ("",1,34)}) "x"))))

            it "do ... end" $
                parse stmt "do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do do end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end"
                `shouldBe` Right (SScope annz{source=("",1,1)} (SScope annz{source=("",1,4)} (SScope annz{source=("",1,7)} (SScope annz{source=("",1,10)} (SScope annz{source=("",1,13)} (SScope annz{source=("",1,16)} (SScope annz{source=("",1,19)} (SScope annz{source=("",1,22)} (SScope annz{source=("",1,25)} (SScope annz{source=("",1,28)} (SScope annz{source=("",1,31)} (SScope annz{source=("",1,34)} (SScope annz{source=("",1,37)} (SScope annz{source=("",1,40)} (SScope annz{source=("",1,43)} (SScope annz{source=("",1,46)} (SScope annz{source=("",1,49)} (SScope annz{source=("",1,52)} (SScope annz{source=("",1,55)} (SScope annz{source=("",1,58)} (SScope annz{source=("",1,61)} (SScope annz{source=("",1,64)} (SScope annz{source=("",1,67)} (SScope annz{source=("",1,70)} (SScope annz{source=("",1,73)} (SScope annz{source=("",1,76)} (SScope annz{source=("",1,79)} (SScope annz{source=("",1,82)} (SScope annz{source=("",1,85)} (SScope annz{source=("",1,88)} (SScope annz{source=("",1,91)} (SScope annz{source=("",1,94)} (SScope annz{source=("",1,97)} (SScope annz{source=("",1,100)} (SScope annz{source=("",1,103)} (SScope annz{source=("",1,106)} (SScope annz{source=("",1,109)} (SScope annz{source=("",1,112)} (SScope annz{source=("",1,115)} (SScope annz{source=("",1,118)} (SScope annz{source=("",1,121)} (SScope annz{source=("",1,124)} (SScope annz{source=("",1,127)} (SScope annz{source=("",1,130)} (SScope annz{source=("",1,133)} (SScope annz{source=("",1,136)} (SScope annz{source=("",1,139)} (SScope annz{source=("",1,142)} (SScope annz{source=("",1,145)} (SScope annz{source=("",1,148)} (SScope annz{source=("",1,151)} (SScope annz{source=("",1,154)} (SScope annz{source=("",1,157)} (SScope annz{source=("",1,160)} (SScope annz{source=("",1,163)} (SScope annz{source=("",1,166)} (SScope annz{source=("",1,169)} (SScope annz{source=("",1,172)} (SScope annz{source=("",1,175)} (SScope annz{source=("",1,178)} (SScope annz{source=("",1,181)} (SScope annz{source=("",1,184)} (SScope annz{source=("",1,187)} (SScope annz{source=("",1,190)} (SScope annz{source=("",1,193)} (SScope annz{source=("",1,196)} (SScope annz{source=("",1,199)} (SScope annz{source=("",1,202)} (SScope annz{source=("",1,205)} (SScope annz{source=("",1,208)} (SScope annz{source=("",1,211)} (SScope annz{source=("",1,214)} (SScope annz{source=("",1,217)} (SScope annz{source=("",1,220)} (SScope annz{source=("",1,223)} (SScope annz{source=("",1,226)} (SScope annz{source=("",1,229)} (SScope annz{source=("",1,232)} (SScope annz{source=("",1,235)} (SScope annz{source=("",1,238)} (SScope annz{source=("",1,241)} (SScope annz{source=("",1,244)} (SScope annz{source=("",1,247)} (SScope annz{source=("",1,250)} (SScope annz{source=("",1,253)} (SScope annz{source=("",1,256)} (SScope annz{source=("",1,259)} (SScope annz{source=("",1,262)} (SScope annz{source=("",1,265)} (SScope annz{source=("",1,268)} (SScope annz{source=("",1,271)} (SScope annz{source=("",1,274)} (SScope annz{source=("",1,277)} (SScope annz{source=("",1,280)} (SScope annz{source=("",1,283)} (SScope annz{source=("",1,286)} (SScope annz{source=("",1,289)} (SScope annz{source=("",1,292)} (SScope annz{source=("",1,295)} (SScope annz{source=("",1,298)} (SScope annz{source=("",1,301)} (SScope annz{source=("",1,304)} (SScope annz{source=("",1,307)} (SScope annz{source=("",1,310)} (SScope annz{source=("",1,313)} (SScope annz{source=("",1,316)} (SScope annz{source=("",1,319)} (SScope annz{source=("",1,322)} (SScope annz{source=("",1,325)} (SScope annz{source=("",1,328)} (SScope annz{source=("",1,331)} (SScope annz{source=("",1,334)} (SScope annz{source=("",1,337)} (SScope annz{source=("",1,340)} (SScope annz{source=("",1,343)} (SScope annz{source=("",1,346)} (SScope annz{source=("",1,349)} (SScope annz{source=("",1,352)} (SScope annz{source=("",1,355)} (SScope annz{source=("",1,358)} (SScope annz{source=("",1,361)} (SScope annz{source=("",1,364)} (SScope annz{source=("",1,367)} (SScope annz{source=("",1,370)} (SScope annz{source=("",1,373)} (SScope annz{source=("",1,376)} (SScope annz{source=("",1,379)} (SScope annz{source=("",1,382)} (SScope annz{source=("",1,385)} (SScope annz{source=("",1,388)} (SScope annz{source=("",1,391)} (SScope annz{source=("",1,394)} (SScope annz{source=("",1,397)} (SScope annz{source=("",1,400)} (SScope annz{source=("",1,403)} (SScope annz{source=("",1,406)} (SScope annz{source=("",1,409)} (SScope annz{source=("",1,412)} (SScope annz{source=("",1,415)} (SScope annz{source=("",1,418)} (SScope annz{source=("",1,421)} (SScope annz{source=("",1,424)} (SScope annz{source=("",1,427)} (SScope annz{source=("",1,430)} (SScope annz{source=("",1,433)} (SScope annz{source=("",1,436)} (SScope annz{source=("",1,439)} (SScope annz{source=("",1,442)} (SScope annz{source=("",1,445)} (SScope annz{source=("",1,448)} (SScope annz{source=("",1,451)} (SScope annz{source=("",1,454)} (SScope annz{source=("",1,457)} (SScope annz{source=("",1,460)} (SScope annz{source=("",1,463)} (SScope annz{source=("",1,466)} (SScope annz{source=("",1,469)} (SScope annz{source=("",1,472)} (SScope annz{source=("",1,475)} (SScope annz{source=("",1,478)} (SScope annz{source=("",1,481)} (SScope annz{source=("",1,484)} (SScope annz{source=("",1,487)} (SScope annz{source=("",1,490)} (SScope annz{source=("",1,493)} (SScope annz{source=("",1,496)} (SScope annz{source=("",1,499)} (SScope annz{source=("",1,502)} (SScope annz{source=("",1,505)} (SScope annz{source=("",1,508)} (SScope annz{source=("",1,511)} (SScope annz{source=("",1,514)} (SScope annz{source=("",1,517)} (SScope annz{source=("",1,520)} (SScope annz{source=("",1,523)} (SScope annz{source=("",1,526)} (SScope annz{source=("",1,529)} (SScope annz{source=("",1,532)} (SScope annz{source=("",1,535)} (SScope annz{source=("",1,538)} (SScope annz{source=("",1,541)} (SScope annz{source=("",1,544)} (SScope annz{source=("",1,547)} (SScope annz{source=("",1,550)} (SScope annz{source=("",1,553)} (SScope annz{source=("",1,556)} (SScope annz{source=("",1,559)} (SScope annz{source=("",1,562)} (SScope annz{source=("",1,565)} (SScope annz{source=("",1,568)} (SScope annz{source=("",1,571)} (SScope annz{source=("",1,574)} (SScope annz{source=("",1,577)} (SScope annz{source=("",1,580)} (SScope annz{source=("",1,583)} (SScope annz{source=("",1,586)} (SScope annz{source=("",1,589)} (SScope annz{source=("",1,592)} (SScope annz{source=("",1,595)} (SScope annz{source=("",1,598)} (SScope annz{source=("",1,601)} (SScope annz{source=("",1,604)} (SScope annz{source=("",1,607)} (SScope annz{source=("",1,610)} (SScope annz{source=("",1,613)} (SScope annz{source=("",1,616)} (SScope annz{source=("",1,619)} (SScope annz{source=("",1,622)} (SScope annz{source=("",1,625)} (SScope annz{source=("",1,628)} (SScope annz{source=("",1,631)} (SScope annz{source=("",1,634)} (SScope annz{source=("",1,637)} (SScope annz{source=("",1,640)} (SScope annz{source=("",1,643)} (SScope annz{source=("",1,646)} (SScope annz{source=("",1,649)} (SScope annz{source=("",1,652)} (SScope annz{source=("",1,655)} (SScope annz{source=("",1,658)} (SScope annz{source=("",1,661)} (SScope annz{source=("",1,664)} (SScope annz{source=("",1,667)} (SScope annz{source=("",1,670)} (SScope annz{source=("",1,673)} (SScope annz{source=("",1,676)} (SScope annz{source=("",1,679)} (SScope annz{source=("",1,682)} (SScope annz{source=("",1,685)} (SScope annz{source=("",1,688)} (SScope annz{source=("",1,691)} (SScope annz{source=("",1,694)} (SScope annz{source=("",1,697)} (SScope annz{source=("",1,700)} (SScope annz{source=("",1,703)} (SScope annz{source=("",1,706)} (SScope annz{source=("",1,709)} (SScope annz{source=("",1,712)} (SScope annz{source=("",1,715)} (SScope annz{source=("",1,718)} (SScope annz{source=("",1,721)} (SScope annz{source=("",1,724)} (SScope annz{source=("",1,727)} (SScope annz{source=("",1,730)} (SScope annz{source=("",1,733)} (SScope annz{source=("",1,736)} (SScope annz{source=("",1,739)} (SScope annz{source=("",1,742)} (SScope annz{source=("",1,745)} (SScope annz{source=("",1,748)} (SScope annz{source=("",1,751)} (SScope annz{source=("",1,754)} (SScope annz{source=("",1,757)} (SScope annz{source=("",1,760)} (SScope annz{source=("",1,763)} (SScope annz{source=("",1,766)} (SNop annz{source=("",1,769)})))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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

        parse'' rule src = case parse rule src of
                            Left  err -> Left err
                            Right exp -> Right $ clearExp exp
