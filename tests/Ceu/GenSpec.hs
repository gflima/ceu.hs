{-# LANGUAGE QuasiQuotes #-}

module Ceu.GenSpec (main, spec) where

import Test.Hspec
import Text.RawString.QQ
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

      describe "basic:" $ do

        it "IEq" $
          (run True $
            unlines [
              "interface IEq for a with"         ,
              " var eq  : ((a,a) -> Int)"         ,
              " var neq : ((a,a) -> Int)"         ,
              "end"                               ,
              "return 1"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default" $
          (run True $
            unlines [
              "interface IEq for a with"         ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "return 1"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return neq(10,20)"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int + f" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "func f x : (a -> Int) where a is IEq do",
              "   return x eq x",   -- eq_a
              "end",
              "return f 1"  -- eq_a=eq_Int
             ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + f + Int" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "func f x : (a -> Int) where a is IEq do",
              "   return x eq x",   -- eq_a
              "end",
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return f 1"  -- eq_a=eq_Int
             ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "no-fields" $
          (run True $
            unlines [
              "interface IFa for a with end",
              "implementation of IFa for Bool with end",
              "return Bool.True"
             ])
          `shouldBe` Right (EData ["Bool","True"] EUnit)

      describe "extends:" $ do

        it "IOrd extends IEq" $
          (run True $
            unlines [
              "interface IOrd for a where (a is IEq) with",
              "   func =>= : ((a,a) -> Bool)",
              "end",
              "",
              "implementation of (IOrd for Bool) with",
              "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x end",
              "end",
              "",
              "return (Bool.True) =>= (Bool.False)"
            ])
          `shouldBe` Left "(line 1, column 1):\ninterface 'IEq' is not declared\n(line 5, column 1):\nimplementation 'IEq for Bool' is not declared\n"

        it "IOrd extends IEq" $
          (run True $
            unlines [
              "interface IEq for a with",
              "   func === : ((a,a) -> Bool)",
              "end",
              "",
              "interface (IOrd for a) where (a is IEq) with",
              "   func =>= : ((a,a) -> Bool)",
              "end",
              "",
              "implementation of (IOrd for Bool) with",
              "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x === y end",
              "end",
              "",
              "return (Bool.True) =>= (Bool.False)"
            ])
          `shouldBe` Left "(line 9, column 1):\nimplementation 'IEq for Bool' is not declared\n(line 10, column 55):\nvariable '===' has no associated implementation for '((Bool,Bool) -> Bool)'\n"
          --`shouldBe` Left "(line 9, column 1):\nimplementation 'IEq for Bool' is not declared\n"

        it "IOrd extends IEq" $
          (run True $
            unlines [
              "interface IEq for a with",
              "   func === : ((a,a) -> Bool)",
              "end",
              "",
              "interface (IOrd for a) where (a is IEq) with",
              "   func =>= : ((a,a) -> Bool)",
              "end",
              "",
              "implementation of IEq for Bool with" ,
              " func === (x,y) : ((Bool,Bool) -> Bool) do",
              "   return Bool.True"                  ,
              " end"                              ,
              "end"                               ,
              "",
              "implementation of (IOrd for Bool) with",
              "   func =>= (x,y) : ((Bool,Bool) -> Bool) do return x === y end",
              "end",
              "",
              "return (Bool.True) =>= (Bool.False)"
            ])
          `shouldBe` Right (EData ["Bool","True"] EUnit)

        it "implementation for extends of (a,b)" $
          (run True $
            unlines [
              "interface IFa for a with end",
              --"implementation of IFa for (a,b) where (a,b) is (IFa,IFa) with end",
              "interface IFb for a where (a is IFa) with end",
              "implementation of IFb for (a,b) where (a is IFb, b is IFb) with end",
              "return Bool.True"
             ])
          `shouldBe` Left "(line 3, column 1):\nimplementation 'IFa for (a,b) where (a is IFb,b is IFb)' is not declared\n"

        it "IEq/IOrd" $
          (run True $
            [r|
interface IEqualable for a with
  func eq : ((a,a) -> Bool)
end

implementation of IEqualable for Int with
  func eq (x,y) : ((Int,Int) -> Bool) do
    return x == y
  end
end

implementation of IEqualable for Bool with
  func eq (x,y) : ((Bool,Bool) -> Bool) do
    call print 111
    return Bool.True
  end
end

interface IOrderable for a where (a is IEqualable) with
  func lte (x,y) : ((a,a) -> Bool) do return (x eq y) end
end

implementation of IOrderable for Int with
end

return 30 lte 25
|])
          `shouldBe` Right (EData ["Bool","False"] EUnit)

      describe "gen-inst:" $ do

        it "TODO (Ee does not impl. IXxx): IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
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
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y))",
              " end"                              ,
              "end"                               ,
              "data Ee",
              "return (eq(Ee,Ee))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "AAA: IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
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
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y))",
              " end"                              ,
              "end"                               ,
              "return (eq(Dd,Dd))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
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
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y))",
              " end"                              ,
              "end"                               ,
              "return (eq(Dd,Dd))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
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
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y)) + (1 eq 1)",
              " end"                              ,
              "end"                               ,
              "return (eq(Dd,Dd)) + (eq(Ee,Ee))"
            ])
          `shouldBe` Right (EData ["Int","4"] EUnit)

        it "XXX-0: IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " func eq : ((a,a) -> Int)"         ,
              "end"                               ,
              "interface IXx for a with"          ,
              " var f : (a -> Int)"               ,
              "end"                               ,
              "data Dd"                           ,
              "implementation of IXx for Dd with" ,
              " func f (x) : (Dd -> Int) do"      ,
              "   return 1"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return f x",
              " end"                              ,
              "end"                               ,
              "return eq (Dd,Dd)"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "TODO (dependency inversion): IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " func eq : ((a,a) -> Int)"         ,
              "end"                               ,
              "interface IXx for a with"          ,
              " var f : (a -> Int)"               ,
              "end"                               ,
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return f x",
              " end"                              ,
              "end"                               ,
              "data Dd"                           ,
              "implementation of IXx for Dd with" ,
              " func f (x) : (Dd -> Int) do"      ,
              "   return 1"                       ,
              " end"                              ,
              "end"                               ,
              "return eq (Dd,Dd)"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "XXX-1: IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "interface IXx for a with"          ,
              " var f : (a -> Int)"               ,
              "end"                               ,
              "interface IYy for a with"          ,
              " var g : (a -> Int)"               ,
              "end"                               ,
              "data Dd",
              "implementation of IXx for Dd with" ,
              " func f (x) : (Dd -> Int) do"    ,
              "   return 1"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y)) + (1 eq 1)",
              " end"                              ,
              "end"                               ,
              "implementation of IEq for a where a is IYy with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((g x) eq (g y)) + (1 eq 1)",
              " end"                              ,
              "end"                               ,
              "return eq (Dd,Dd)"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "interface IXx for a with"          ,
              " var f : (a -> Int)"               ,
              "end"                               ,
              "interface IYy for a with"          ,
              " var g : (a -> Int)"               ,
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
              "data Ff",
              "implementation of IYy for Ff with" ,
              " func g (x) : (Ff -> Int) do"    ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for a where a is IXx with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((f x) eq (f y)) + (1 eq 1)",
              " end"                              ,
              "end"                               ,
              "implementation of IEq for a where a is IYy with" ,
              " func eq (x,y) : ((a,a) -> Int) do" ,
              "   return ((g x) eq (g y)) + (1 eq 1)",
              " end"                              ,
              "end"                               ,
              "return ((eq(Dd,Dd)) + (eq(Ee,Ee))) + (eq(Ff,Ff))"
            ])
          `shouldBe` Right (EData ["Int","4"] EUnit)

        it "IEq + default + Int + (a,b)" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b) where (a is IEq, b is IEq) with" ,
              " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
              "   if (x eq z) matches 1 then"                 ,   -- eq_a
              "     if (y eq w) matches 1 then"               ,   -- eq_b
              "       return 1"                   ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "return eq( eq(10,10), eq((10,20),(10,20)) )"            -- eq_a=eq_Int, eq_b=eq_Int
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int + (a,b)" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b) where (a is IEq,b is IEq) with" ,
              " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
              "   if (x eq z) matches 1 then"                 ,   -- eq_a
              "     if (y eq w) matches 1 then"               ,   -- eq_b
              "       return 1"                   ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "return eq( eq(10,20), eq((10,20),(30,40)) )"            -- eq_a=eq_Int, eq_b=eq_Int
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IAa / Int / X a" $
          (run True $ [r|
interface IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

implementation of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

data X for a with a

implementation of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var v : a
    set (X v) = x
    return f v
  end
end

return (((f 10) + (g 10)) + (f (X 10))) + (g (X 10))
|])
          `shouldBe` Right (EData ["Int","40"] EUnit)

        it "IAa / Int / X a a" $
          (run True $ [r|
interface IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

implementation of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

data X for a with (a,a)

implementation of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var (v1,v2) : (a,a)
    set X (v1,v2) = x
    return (f v1) + (f v2)
  end
end

return (((f 10) + (g 10)) + (f (X (10,20)))) + (g (X (10,20)))
|])
          `shouldBe` Right (EData ["Int","80"] EUnit)

        it "IAa / X a a / Int" $
          (run True $ [r|
interface IAa for a with
  var f : (a -> Int)
end

data X for a with a

implementation of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var v1 : a
    set X v1 = x
    return (f v1)
  end
end

implementation of IAa for () with
  func f (x) : (() -> Int) do
    return 1
  end
end

return f (X ())
|])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IAa / X a a / Int" $
          (run True $ [r|
interface IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

data X for a with (a,a)

implementation of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var (v1,v2) : (a,a)
    set X (v1,v2) = x
    return (f v1) + (f v2)
  end
end

implementation of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

return (((f 10) + (g 10)) + (f (X (10,20)))) + (g (X (10,20)))
|])
          `shouldBe` Right (EData ["Int","80"] EUnit)

        it "IEq + default + Int + (a,b)" $ -- CASE-1 eq(a,b) is not SUP of eq(Int)
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for (a,b) where (a is IEq, b is IEq) with" ,
              " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
              "   if (x eq z) matches 1 then"                 ,   -- eq_a
              "     if (y eq w) matches 1 then"               ,   -- eq_b
              "       return 1"                   ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return (eq((10,20),(30,40))) + (neq((10,20),(30,40)))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int + (a,b) + Bool" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for Bool with" ,
              " func eq (x,y) : ((Bool,Bool) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b) where (a is IEq, b is IEq) with" ,
              " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
              "   if (x eq z) matches 1 then"                 ,   -- eq_a
              "     if (y eq w) matches 1 then"               ,   -- eq_b
              "       return 1"                   ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "return eq((10,Bool.True),(10,Bool.True))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int + (a,b) + Bool" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b) where (a is IEq, b is IEq) with" ,
              " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
              "   if (x eq z) matches 1 then"                 ,   -- eq_a
              "     if (y eq w) matches 1 then"               ,   -- eq_b
              "       return 1"                   ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for Bool with" ,
              " func eq (x,y) : ((Bool,Bool) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return eq((10,Bool.True),(20,Bool.False))"
            ])
          `shouldBe` Right (EData ["Int","0"] EUnit)

{-
      it "TODO-TIME: IEq + default + Int + (a,b,c) + Bool" $
        (run True $
          unlines [
            "interface IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "implementation of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if ~x matches y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "implementation of IEq for (a,b,c) where (a is IEq,b is IEq,c is IEq) with" ,
            " func eq ((x,y,z),(i,j,k)) : (((a,b,c),(a,b,c)) -> Int) do",
            "   if 1 matches x eq i then"            ,
            "     if 1 matches y eq j then"          ,
            "       if 1 matches z eq k then"        ,
            "         return 1"                 ,
            "       end"                        ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "implementation of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if ~x matches y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return eq((20,Bool.True,10),(20,Bool.True,10))"
          ])
        `shouldBe` Right (EData ["Int","1"] EUnit)
-}

        it "IEq + default + Int + (a,b,a) + Bool" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b,a) where (a is IEq,b is IEq) with" ,
              " func eq ((x,y,z),(i,j,k)) : (((a,b,a),(a,b,a)) -> Int) do",
              "   if (x eq i) matches 1 then"            ,
              "     if (y eq j) matches 1 then"          ,
              "       if (z eq k) matches 1 then"        ,
              "         return 1"                 ,
              "       end"                        ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for Bool with" ,
              " func eq (x,y) : ((Bool,Bool) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return eq((20,Bool.True,10),(20,Bool.True,10))"
            ])
          `shouldBe` Right (EData ["Int","1"] EUnit)

        it "IEq + default + Int + (a,b,a) + Bool" $
          (run True $
            unlines [
              "interface IEq for a with"          ,
              " var eq  : ((a,a) -> Int)"         ,
              " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
              "end"                               ,
              "implementation of IEq for Int with" ,
              " func eq (x,y) : ((Int,Int) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for (a,b,a) where (a is IEq, b is IEq) with" ,
              " func eq ((x,y,z),(i,j,k)) : (((a,b,a),(a,b,a)) -> Int) do",
              "   if (x eq i) matches 1 then"            ,
              "     if (y eq j) matches 1 then"          ,
              "       if (z eq k) matches 1 then"        ,
              "         return 1"                 ,
              "       end"                        ,
              "     end"                          ,
              "   end"                            ,
              "   return 0"                       ,
              " end"                              ,
              "end"                               ,
              "implementation of IEq for Bool with" ,
              " func eq (x,y) : ((Bool,Bool) -> Int) do",
              "   if y matches x then return 1 else return 0 end"                  ,
              " end"                              ,
              "end"                               ,
              "return eq((20,10,Bool.True),(20,10,Bool.True))"
            ])
          `shouldBe` Left "(line 27, column 8):\nvariable 'eq' has no associated implementation for '(((Int,Int,Bool.True),(Int,Int,Bool.True)) -> ?)'\n"

        it "X for a with a" $
          (run True $ [r|
data X for a with a
interface IFable for a with
  func f : (a -> Int)
end
interface IGable for a with
  func g : (a -> Int)
end
implementation of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
implementation of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v = x
    return f v
  end
end
var x1 : X of Int = X 10
return (g x1)
|])
          `shouldBe` Right (EData ["Int","10"] EUnit)

        it "X for a with a" $
          (run True $ [r|
data X for a with a
interface IFable for a with
  func f : (a -> Int)
end
interface IGable for a with
  func g : (a -> Int)
end
implementation of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v = x
    return f v
  end
end
implementation of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
var x1 : X of Int = X 10
return (g x1)
|])
          `shouldBe` Right (EData ["Int","10"] EUnit)

        it "X for a with a" $
          (run True $ [r|
data X for a with a
data Y
interface IFable for a with
  func f : (a -> Int)
end
interface IGable for a with
  func g : (a -> Int)
end
implementation of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
implementation of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v = x
    return f v
  end
end
var x2 : X of Y = X Y
return (g x2)
|])
          `shouldBe` Left "(line 23, column 9):\nvariable 'g' has no associated implementation for '((X of Y) -> ?)'\n"

        it "X for a w/o a" $
          (run True $ [r|
data X   for a
data X.Y with a
interface IFable for a with
  func f : (a -> Int)
end
interface IGable for a with
  func g : (a -> Int)
end
implementation of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
implementation of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    match x with
      case X.Y =v : Int then
        return f v
      else
        return 0
    end
  end
end
var x1 : X of Int = X.Y 10
var x2 : X of Int = X
return (g x1) + (g x2)
|])
          `shouldBe` Right (EData ["Int","10"] EUnit)

        it "X for a w/o a" $
          (run True $ [r|
data X   for a
data X.Y with a
data Z
interface IFable for a with
  func f : (a -> Int)
end
interface IGable for a with
  func g : (a -> Int)
end
implementation of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
implementation of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    match x with
      case X.Y =v : Int then
        return f v
      else
        return 0
    end
  end
end
var x1 : X of Z = X.Y Z
var x2 : X of Z = X
return (g x1) + (g x2)
|])
          `shouldBe` Left "(line 28, column 9):\nvariable 'g' has no associated implementation for '((X of Z) -> ?)'\n(line 28, column 18):\nvariable 'g' has no associated implementation for '((X of Z) -> ?)'\n"

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
          "   if x matches Bool.True then",
          "     return Bool.False",
          "   else",
          "     return Bool.True",
          "   end",
          "end",
          "",
          "func and (x,y) : ((Bool,Bool)->Bool) do",
          "   if x matches Bool.False then",
          "     return Bool.False",
          "   else",
          "     return y",
          "   end",
          "end",
          "",
          "interface IEqualable for a with",
          "   func === (x,y) : ((a,a) -> Bool) do",
          "     if y matches x then",
          "       if x matches y then",
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
