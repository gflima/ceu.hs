{-# LANGUAGE QuasiQuotes #-}

module Ceu.ClassSpec (main, spec) where

import Test.Hspec
import Text.RawString.QQ

import qualified Ceu.Grammar.Constraints as Cs
import qualified Ceu.Grammar.Type        as T

import Ceu.Grammar.Full.Compile.Class

main :: IO ()
main = hspec spec

spec :: Spec
spec = do

  describe "interface:" $ do

    it "KKK" $
      (test [] (T.TUnit,[("a",["IEq","IShow"]),("b",["IObj"])]))
      `shouldBe` []
