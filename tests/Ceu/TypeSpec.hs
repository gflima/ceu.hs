module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "supOf'" $ do

    it "Int > BOT" $
      Type1 "Int" `supOf'` TypeB       `shouldBe` (True,  TypeB,       [])
    it "BOT > Int" $
      TypeB       `supOf'` Type1 "Int" `shouldBe` (False, TypeB,       [])
    it "a > Int" $
      TypeV "a"   `supOf'` Type1 "Int" `shouldBe` (True,  Type1 "Int", [("a",Type1 "Int")])
    it "a > b" $
      TypeV "a"   `supOf'` TypeV "b"   `shouldBe` (True,  TypeV "b",   [("a",TypeV "b")])

  describe "supOf" $ do

    it "(a -> a) > (Int -> Int)" $
      TypeF (TypeV "a") (TypeV "a") `supOf` TypeF (Type1 "Int") (Type1 "Int")
      `shouldBe` Right ((TypeF (Type1 "Int") (Type1 "Int")), [("a", Type1 "Int")])

    it "(a -> a) > (Int -> ())" $
      TypeF (TypeV "a") (TypeV "a") `supOf` TypeF (Type1 "Int") Type0
      `shouldBe` Left ["types do not match : expected '(a -> a)' : found '(Int -> ())'","ambigous instances for 'a' : 'Int', '()'"]

    it "(a,b) > (Int,())" $
      TypeN [(TypeV "a"),(TypeV "b")] `supOf` TypeN [(Type1 "Int"),Type0]
      `shouldBe` Right (TypeN [Type1 "Int",Type0],[("a",Type1 "Int"),("b",Type0)])

  describe "instantiate" $ do

    it "A in [...] ~> A" $
      instantiate [("a",Type1 "A"), ("b",Type1 "B")] (Type1 "A")
      `shouldBe` (Type1 "A")

    it "(a,b) in [(a,A),(b,B)] ~> (A,B)" $
      instantiate [("a",Type1 "A"), ("b",Type1 "B")] (TypeN [TypeV "a", TypeV "b"])
      `shouldBe` (TypeN [Type1 "A", Type1 "B"])

    it "(a->C) in [(a,A),(b,B)] ~> (A->C)" $
      instantiate [("a",Type1 "A"), ("b",Type1 "B")] (TypeF (TypeV "a") (Type1 "C"))
      `shouldBe` (TypeF (Type1 "A") (Type1 "C"))

    it "Int : (Int ~ Int) ~> Int" $
      inst' (Type1 "Int") (Type1 "Int", Type1 "Int")
      `shouldBe` (Type1 "Int")

    it "Int : (a ~ Int) ~> Int" $
      inst' (Type1 "Int") (TypeV "a", Type1 "Int")
      `shouldBe` (Type1 "Int")

    it "a : (a ~ Int) ~> Int" $
      inst' (TypeV "a") (TypeV "a", Type1 "Int")
      `shouldBe` (Type1 "Int")

    it "a : ((Int,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [Type1 "Int",TypeV "a"], TypeN [Type1 "Int",Type1 "Int"])
      `shouldBe` (Type1 "Int")

    it "a : ((a,Int) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",Type1 "Int"], TypeN [Type1 "Int",Type1 "Int"])
      `shouldBe` (Type1 "Int")

    it "a : ((a,a) ~ (Int,Int)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [Type1 "Int",Type1 "Int"])
      `shouldBe` (Type1 "Int")

    it "a : ((a,a) ~ (Int,Bool)) ~> ERROR" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "a"], TypeN [Type1 "Int",Type1 "Bool"])
      `shouldBe` TypeT

    it "a : ((a,b) ~ (Int,Bool)) ~> Int" $
      inst' (TypeV "a") (TypeN [TypeV "a",TypeV "b"], TypeN [Type1 "Int",Type1 "Bool"])
      `shouldBe` (Type1 "Int")

    it "b : ((a,b) ~ (Int,Bool)) ~> Bool" $
      inst' (TypeV "b") (TypeN [TypeV "a",TypeV "b"], TypeN [Type1 "Int",Type1 "Bool"])
      `shouldBe` (Type1 "Bool")

  where
    inst' :: Type -> (Type,Type) -> Type
    inst' tp (sup,sub) =
      case sup `supOf` sub of
        Right (_,insts) -> instantiate insts tp
        Left _          -> TypeT
