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

    describe "constraint:" $ do

      it "IEq" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " var neq : ((a,a) -> Int)"         ,
            "end"                               ,
            "return 1"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "return 1"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
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
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "func f x : (a -> Int) where a is IEq do",
            "   return x eq x",   -- eq_a
            "end",
            "return f 1"  -- eq_a=eq_Int
           ])
        `shouldBe` Right (Number 1)

      it "IEq + default + f + Int" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "func f x : (a -> Int) where a is IEq do",
            "   return x eq x",   -- eq_a
            "end",
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return f 1"  -- eq_a=eq_Int
           ])
        `shouldBe` Right (Number 1)

      it "IEq + default + $Int$ + IXx + $Dd$ + $Ee$ + $IXx$" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "constraint IXx for a with"          ,
            " var f : (a -> Int)"               ,
            "end"                               ,
            "data Dd",
            "instance of IXx for Dd with" ,
            " func f (x) : (Dd -> Int) do"    ,
            "   return 1"                       ,
            " end"                              ,
            "end"                               ,
            "data Ee",
            "instance of IXx for Ee with" ,
            " func f (x) : (Ee -> Int) do"    ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for a where a is IXx with" ,
            " func eq (x,y) : ((a,a) -> Int) do" ,
            "   return ((f x) eq (f y)) + (1 eq 1)",
            " end"                              ,
            "end"                               ,
            "return (eq(Dd,Dd)) + (eq(Ee,Ee))"
          ])
        `shouldBe` Right (Number 4)

      it "IEq + default + Int + (a,b)" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b) where (a is IEq, b is IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if 1 <- (x eq z) then"                 ,   -- eq_a
            "     if 1 <- (y eq w) then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "return eq( eq(10,10), eq((10,20),(10,20)) )"            -- eq_a=eq_Int, eq_b=eq_Int
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int + (a,b)" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b) where (a is IEq,b is IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if 1 <- (x eq z) then"                 ,   -- eq_a
            "     if 1 <- (y eq w) then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "return eq( eq(10,20), eq((10,20),(30,40)) )"            -- eq_a=eq_Int, eq_b=eq_Int
          ])
        `shouldBe` Right (Number 1)

      it "IAa / Int / X a" $
        (run True $ [r|
constraint IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

instance of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

data X for a with a

instance of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var v : a
    set (X v) <- x
    return f v
  end
end

return (((f 10) + (g 10)) + (f (X 10))) + (g (X 10))
|])
        `shouldBe` Right (Number 40)

      it "IAa / Int / X a a" $
        (run True $ [r|
constraint IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

instance of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

data X for a with (a,a)

instance of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var (v1,v2) : (a,a)
    set X (v1,v2) <- x
    return (f v1) + (f v2)
  end
end

return (((f 10) + (g 10)) + (f (X (10,20)))) + (g (X (10,20)))
|])
        `shouldBe` Right (Number 80)

      it "IAa / X a a / Int" $
        (run True $ [r|
constraint IAa for a with
  var f : (a -> Int)
  func g (x) : (a -> Int) do
    return f x
  end
end

data X for a with (a,a)

instance of IAa for (X of a) where (a is IAa) with
  func f (x) : (X of a -> Int) do
    var (v1,v2) : (a,a)
    set X (v1,v2) <- x
    return (f v1) + (f v2)
  end
end

instance of IAa for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end

return (((f 10) + (g 10)) + (f (X (10,20)))) + (g (X (10,20)))
|])
        `shouldBe` Right (Number 80)

      it "IEq + default + Int + (a,b)" $ -- CASE-1 eq(a,b) is not SUP of eq(Int)
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for (a,b) where (a is IEq, b is IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if 1 <- (x eq z) then"                 ,   -- eq_a
            "     if 1 <- (y eq w) then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return (eq((10,20),(30,40))) + (neq((10,20),(30,40)))"
          ])
        `shouldBe` Right (Number 1)

      it "IEq + default + Int + (a,b) + Bool" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b) where (a is IEq, b is IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if 1 <- x eq z then"                 ,   -- eq_a
            "     if 1 <- y eq w then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "return eq((10,Bool.True),(10,Bool.True))"
          ])
        `shouldBe` Right (Number 1)

      it "YYY: IEq + default + Int + (a,b) + Bool" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b) where (a is IEq, b is IEq) with" ,
            " func eq ((x,y),(z,w)) : (((a,b),(a,b)) -> Int) do",
            "   if 1 <- x eq z then"                 ,   -- eq_a
            "     if 1 <- y eq w then"               ,   -- eq_b
            "       return 1"                   ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return eq((10,Bool.True),(20,Bool.False))"
          ])
        `shouldBe` Right (Number 0)

      it "XXX: IEq + default + Int + (a,b,c) + Bool" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b,c) where (a is IEq,b is IEq,c is IEq) with" ,
            " func eq ((x,y,z),(i,j,k)) : (((a,b,c),(a,b,c)) -> Int) do",
            "   if 1 <- x eq i then"            ,
            "     if 1 <- y eq j then"          ,
            "       if 1 <- z eq k then"        ,
            "         return 1"                 ,
            "       end"                        ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return eq((20,Bool.True,10),(20,Bool.True,10))"
          ])
        `shouldBe` Right (Number 1)

      it "YYY: IEq + default + Int + (a,b,a) + Bool" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b,a) where (a is IEq,b is IEq) with" ,
            " func eq ((x,y,z),(i,j,k)) : (((a,b,a),(a,b,a)) -> Int) do",
            "   if 1 <- x eq i then"            ,
            "     if 1 <- y eq j then"          ,
            "       if 1 <- z eq k then"        ,
            "         return 1"                 ,
            "       end"                        ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return eq((20,Bool.True,10),(20,Bool.True,10))"
          ])
        `shouldBe` Right (Number 1)

      it "YYY: IEq + default + Int + (a,b,a) + Bool" $
        (run True $
          unlines [
            "constraint IEq for a with"          ,
            " var eq  : ((a,a) -> Int)"         ,
            " func neq (x,y) : ((a,a) -> Int) do return 1 - (x eq y) end",
            "end"                               ,
            "instance of IEq for Int with" ,
            " func eq (x,y) : ((Int,Int) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for (a,b,a) where (a is IEq, b is IEq) with" ,
            " func eq ((x,y,z),(i,j,k)) : (((a,b,a),(a,b,a)) -> Int) do",
            "   if 1 <- x eq i then"            ,
            "     if 1 <- y eq j then"          ,
            "       if 1 <- z eq k then"        ,
            "         return 1"                 ,
            "       end"                        ,
            "     end"                          ,
            "   end"                            ,
            "   return 0"                       ,
            " end"                              ,
            "end"                               ,
            "instance of IEq for Bool with" ,
            " func eq (x,y) : ((Bool,Bool) -> Int) do",
            "   if `x´ <- y then return 1 else return 0 end"                  ,
            " end"                              ,
            "end"                               ,
            "return eq((20,10,Bool.True),(20,10,Bool.True))"
          ])
        `shouldBe` Left "(line 27, column 8):\nvariable 'eq' has no associated instance for '(((Int.20,Int.10,Bool.True),(Int.20,Int.10,Bool.True)) -> ?)'\n"

      it "X for a with a" $
        (run True $ [r|
data X for a with a
constraint IFable for a with
  func f : (a -> Int)
end
constraint IGable for a with
  func g : (a -> Int)
end
instance of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
instance of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v <- x
    return f v
  end
end
var x1 : X of Int <- X 10
return (g x1)
|])
        `shouldBe` Right (Number 10)

      it "X for a with a" $
        (run True $ [r|
data X for a with a
constraint IFable for a with
  func f : (a -> Int)
end
constraint IGable for a with
  func g : (a -> Int)
end
instance of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v <- x
    return f v
  end
end
instance of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
var x1 : X of Int <- X 10
return (g x1)
|])
        `shouldBe` Right (Number 10)

      it "X for a with a" $
        (run True $ [r|
data X for a with a
data Y
constraint IFable for a with
  func f : (a -> Int)
end
constraint IGable for a with
  func g : (a -> Int)
end
instance of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
instance of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    set X v <- x
    return f v
  end
end
var x2 : X of Y <- X Y
return (g x2)
|])
        `shouldBe` Left "(line 23, column 9):\nvariable 'g' has no associated instance for '((X of Y) -> ?)'\n"

      it "X for a w/o a" $
        (run True $ [r|
data X   for a
data X.Y with a
constraint IFable for a with
  func f : (a -> Int)
end
constraint IGable for a with
  func g : (a -> Int)
end
instance of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
instance of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    if X.Y v <- x then
      return f v
    else
      return 0
    end
  end
end
var x1 : X of Int <- X.Y 10
var x2 : X of Int <- X
return (g x1) + (g x2)
|])
        `shouldBe` Right (Number 10)

      it "X for a w/o a" $
        (run True $ [r|
data X   for a
data X.Y with a
data Z
constraint IFable for a with
  func f : (a -> Int)
end
constraint IGable for a with
  func g : (a -> Int)
end
instance of IFable for Int with
  func f (x) : (Int -> Int) do
    return x
  end
end
instance of IGable for (X of a) where (a is IFable) with
  func g (x) : ((X of a) -> Int) do
    var v : a
    if X.Y v <- x then
      return f v
    else
      return 0
    end
  end
end
var x1 : X of Z <- X.Y Z
var x2 : X of Z <- X
return (g x1) + (g x2)
|])
        `shouldBe` Left "(line 28, column 9):\nvariable 'g' has no associated instance for '((X of Z) -> ?)'\n(line 28, column 18):\nvariable 'g' has no associated instance for '((X of Z) -> ?)'\n"

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
          "constraint IEqualable for a with",
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
