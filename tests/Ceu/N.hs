module Test.NSpec (main, spec) where

import Test.Hspec

import Ceu.Grammar.Globals  (Source)
import Ceu.Grammar.Ann.All
import Ceu.Grammar.Exp      (Exp(..))

import Ceu.Code.N

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "expr:" $ do
        it "1" $
            expr 0 (Const ("",1,1) 1)
            `shouldBe` (1, Const All{source=("",1,1),n=0,trails=(0,0)} 1)
        it "(1,2)" $
            expr 0 (Tuple ("",1,1) [Const ("",1,1) 1, Const ("",1,1) 2])
            `shouldBe` (3,Tuple (All {source = ("",1,1), n = 0, trails = (0,0)}) [Const (All {source = ("",1,1), n = 2, trails = (0,0)}) 1,Const (All {source = ("",1,1), n = 1, trails = (0,0)}) 2])
