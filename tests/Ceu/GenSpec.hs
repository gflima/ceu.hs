module Ceu.GenSpec (main, spec) where

import Test.Hspec
import Data.Bool             (bool)
import Debug.Trace
import Text.Parsec           (parse)

import Ceu.Eval              (Exp(..))
import Ceu.Grammar.Ann       (annz)
import Ceu.Grammar.Full.Eval (go, prelude)
import Ceu.Parser.Stmt       (prog)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

    describe "interface:" $ do

      it "IEq" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " var neq : ((a,a) -> Int)"         ,
            "end"                               ,
            "return 1"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "return 1"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return neq(10,20)"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int + f" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "func f x : (a -> Int) where a implements IEq do",
            "   return x eq x",   -- eq_a
            "end",
            "return f 1"  -- eq_a=eq_Int
           ])
        `shouldBe` Right (Number 1)

      it "XXX: IEq + default + f + Int" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "func f x : (a -> Int) where a implements IEq do",
            "   return x eq x",   -- eq_a
            "end",
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return f 1"  -- eq_a=eq_Int
           ])
        `shouldBe` Right (Number 1)

      it "IEq + default + $Int$ + IXx + $Dd$ + $IXx$" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "interface IXx for a with"          ,
            " var f : (a -> Int)"               ,
            "end"                               ,
            "data Dd",
            "implementation of IXx for Dd with" ,
            " func f (x) : (Dd -> Int) do"    ,
            "   return 1"                       ,
            " end"                              ,
            "end"                               ,
            "data Ee",
            "implementation of IXx for Ee with" ,
            " func f (x) : (Ee -> Int) do"    ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "implementation of IEq for a where a implements IXx with" ,
            " func eq (x,y) : ((a,a) -> Int) do" ,
            "   return ((f x) eq (f y)) + (1 eq 1)",
            " end"                              ,
            "end"                               ,
            "return (eq(Dd,Dd)) + (eq(Ee,Ee))"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int + (a,b)" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "implementation of IEq for (a,b) where (a,b) implements (IEq,IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if x eq z then"                 ,   -- eq_a
            "     if y eq w then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "return eq((10,20),(10,20))"            -- eq_a=eq_Int, eq_b=eq_Int
          ])
        `shouldBe` Right (Number 1)

-------------------------------------------------------------------------------

    where
        run :: Bool -> String -> Either String Exp
        run withPrelude input =
            let v = parse prog "" input in
                case v of
                    (Right p) ->
                      case go $ bool Prelude.id (prelude annz) withPrelude $ p of
                        (Left errs) -> Left $ concatMap (\s->s++"\n") errs
                        (Right exp) -> Right exp
                    (Left  v') -> Left (show v')

        pre = unlines [
          "func not (x) : (Bool->Bool) do",
          "   if Bool.True <- x then",
          "     return Bool.False",
          "   else",
          "     return Bool.True",
          "   end",
          "end",
          "",
          "func and (x,y) : ((Bool,Bool)->Bool) do",
          "   if Bool.False <- x then",
          "     return Bool.False",
          "   else",
          "     return y",
          "   end",
          "end",
          "",
          "interface IEqualable for a with",
          "   func === (x,y) : ((a,a) -> Bool) do",
          "     if `x´ <- y then",
          "       if `y´ <- x then",
          "         return Bool.True",
          "       else",
          "         return Bool.False",
          "       end",
          "     else",
          "       return Bool.False",
          "     end",
          "   end",
          "   func =/= (x,y) : ((a,a) -> Bool) do",
          "     return not (x === y)",
          "   end",
          "end"
         ]
