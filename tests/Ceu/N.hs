module Test.NSpec (main, spec) where

import Test.Hspec

import Ceu.Grammar.Globals  (Source)
import Ceu.Grammar.Ann      (annz, Ann(..))
import Ceu.Grammar.Exp      (Exp(..))

import Ceu.Code.N

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "expr:" $ do
        it "1" $
            expr 0 (Const annz{source=("",1,1)} 1)
            `shouldBe` (1, Const annz{source=("",1,1),nn=0,trails=(0,0)} 1)
        it "(1,2)" $
            expr 0 (Tuple annz{source=("",1,1)} [Const annz{source=("",1,1)} 1, Const annz{source=("",1,1)} 2])
            `shouldBe` (3,Tuple (annz {source = ("",1,1), nn = 0, trails = (0,0)}) [Const (annz {source = ("",1,1), nn = 2, trails = (0,0)}) 1,Const (annz {source = ("",1,1), nn = 1, trails = (0,0)}) 2])
