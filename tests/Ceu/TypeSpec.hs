module Ceu.TypeSpec (main, spec) where

import Debug.Trace
import Test.Hspec

import Ceu.Grammar.Globals
import Ceu.Grammar.Type

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "instantiation" $ do

    it "Int : (Int ~ Int) ~> Int" $
      instantiate (Type1 "Int") (Type1 "Int", Type1 "Int")
      `shouldBe` (Type1 "Int")

    it "Int : (a ~ Int) ~> Int" $
      instantiate (Type1 "Int") (Type1 "a", Type1 "Int")
      `shouldBe` (Type1 "Int")

    it "a : (a ~ Int) ~> Int" $
      instantiate (TypeV "a") (TypeV "a", Type1 "Int")
      `shouldBe` (Type1 "Int")
